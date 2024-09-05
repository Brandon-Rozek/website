---
title: "Webhook notifications on systemd service failure"
date: 2024-09-04T21:03:38-07:00
draft: false
tags: []
math: false
medium_enabled: false
---

Every morning like every good system administrator, I log onto all my machines and type the following command

```bash
systemctl --failed
```

This gives me a list of all my systemd services that have failed. I pray that it's empty

```
  UNIT LOAD ACTIVE SUB DESCRIPTION
0 loaded units listed.

```

Except, I don't.

Instead, I have it set up so that I receive a webhook notification via [Zulip](https://zulip.com) whenever a service fails. With the right infrastructure in place, it's as simple as adding a `OnFailure` line to all the services you want to monitor.

**Step 1:** Setting up the webhook. 

On Zulip, I use the [Slack incoming webhook](https://zulip.com/integrations/doc/slack_incoming) integration. (Note the [URL specification](https://zulip.com/api/incoming-webhooks-overview#url-specification))

As you might guess, this style of webhook works on Slack and on Discord as well.

For our notification script we'll need two environmental variables

| Name        | Description                                                  |
| ----------- | ------------------------------------------------------------ |
| SERVICE     | The name of the `systemd` service. We will automatically populate this |
| WEBHOOK_URL | The URL to send the webhook to. This is chat application specific. |

We'll need the following CLI applications installed

| Name   | Description                                         |
| ------ | --------------------------------------------------- |
| `curl` | Sends the POST request.                             |
| `jq`   | Sanitizes the log output before sending it to curl. |

The script `/bin/webhook-notify.sh`

```bash
#!/bin/bash

if [ -z "$SERVICE" ]; then
    echo "SERVICE variable not set or empty"
    exit 1
fi

if [ -z "$WEBHOOK_URL" ]; then
    echo "WEBHOOK_URL variable not set or empty"
    exit 1
fi

if ! command -v jq &> /dev/null; then
    echo "jq is not installed"
    exit 1
fi

LOG_CONTENTS=$(systemctl status --full --no-pager ${SERVICE} | jq -Rsa .)

curl -X POST --data-urlencode "payload={\"text\": $LOG_CONTENTS}" ${WEBHOOK_URL}
```

Make the script executable

```bash
chmod u+x /bin/webhook-notify.sh
```

At this point you should be able to test out the script and make sure you get notifications. Set the two environmental variables and run the script.

Example:

```bash
export WEBHOOK_URL="https://INSERT-NAMESPCE.zulipchat.com/api/v1/external/slack_incoming?api_key=INSERT-API-KEY&stream=INSERT-STREAM-ID&topic=Systemd"
export SERVICE=NetworkManager
/bin/webhook-notify.sh
```

**Step 2:** Setup the Systemd Service

When a systemd unit fails, we are able to call another systemd service. The service that we'll call will run our script from the last step.

In `/etc/systemd/system/webhook-notify@.service`

```ini
[Unit]
Description=Send Systemd Notifications via Webhook

[Service]
Type=oneshot
Environment=WEBHOOK_URL="INSERT-WEBHOOK-URL-HERE"
Environment=SERVICE=%i
ExecStart=/bin/webhook-notify.sh

[Install]
WantedBy=multi-user.target
```

Note the `@` in the filename. This is important since this service will run with the failed unit name as the argument that appears after the `@`. Within the script, this is the `%i` variable.

Example test:

```bash
sudo systemctl start webhook-notify@NetworkManager
```

**Step 3:** Add `OnFailure` to all the services we want to monitor

Within the `[Unit]` section of our Systemd service, add the following

```ini
OnFailure=webhook-notify@%i.service
```

