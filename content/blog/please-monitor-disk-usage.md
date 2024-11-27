---
title: "Please monitor disk usage"
date: 2024-11-26T19:59:10-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

You know one of the worst errors to deal with on Linux?

> No space left on device

Why? Because recovery becomes really annoying. Depending on your luck, Linux may try to cache to disk even when it's not possible causing several commands to fail.

If you're already in this situation, the best thing you can do is try to locate files to remove.  You can run `du -sh *` in any given directory to see the sizes of files and subfolders.

Common places that hold temporary files which can likely be removed are:

- `/tmp`
- `~/.cache`

An even better solution is to not get into this situation in the first place. For that, I introduce a bash script which sends a notification when the disk is getting full!

In order to see the amount of available and total space for a given `$MOUNTPOINT` (for example, `/`), we run the following:

```bash
available_space=$(df "$MOUNTPOINT" | awk 'NR==2 {print $4}')
total_space=$(df "$MOUNTPOINT" | awk 'NR==2 {print $2}')
```

Add a couple if statements and we have ourselves a full-blown script:

```bash
#!/bin/sh

set -o errexit
set -o nounset

MAX_USAGE_PERCENT=90

if [ -z "$MOUNTPOINT" ]; then
    echo "MOUNTPOINT variable not set or empty"
    exit 1
fi

# Get the available and total disk space for the specified mount point
available_space=$(df "$MOUNTPOINT" | awk 'NR==2 {print $4}')
total_space=$(df "$MOUNTPOINT" | awk 'NR==2 {print $2}')

# Check if the df command was successful
if [ -z "$available_space" ] || [ -z "$total_space" ]; then
    echo "Error: Could not retrieve disk space for $MOUNTPOINT"
    sendMsg "Error: Could not retrieve disk space for $MOUNTPOINT"
    exit 1
fi

usage_percent=$(( (total_space - available_space) * 100 / total_space ))

if [ $usage_percent -ge $MAX_USAGE_PERCENT ]; then
    host_name=$(hostname)
    echo "Low Disk on $host_name at mountpoint $MOUNTPOINT. Currently using ${usage_percent}% of available space."
    sendMsg "Low Disk on $host_name at mountpoint $MOUNTPOINT. Currently using ${usage_percent}% of available space."
fi

echo "Mountpoint $MOUNTPOINT is currently using ${usage_percent}% of available space."
```

The only part left undefined here is the `sendMsg` function. For me, I send a [webhook notification](https://brandonrozek.com/blog/webhook-notifications-on-systemd-service-failure/) to Zulip in order to both get notified and have a log of these messages.

To have this check regularly automatically, we create a systemd service and timer files.

`/etc/systemd/system/lowdiskcheck.service`

```ini
[Unit]
Description=Check for low disk space
Requires=network-online.target
Wants=

[Service]
Type=oneshot
# Feel free to change the mountpoint to one that you care about
Environment=MOUNTPOINT=/home
ExecStart=/usr/local/bin/lowdiskcheck.sh

[Install]
WantedBy=multi-user.target
```

`/etc/systemd/system/lowdiskcheck.timer`

```ini
[Unit]
Description=Check for low disk space daily
[Timer]
OnCalendar=daily
Persistent=true
[Install]
WantedBy=timers.target
```

Then enable the timer,

```bash
sudo systemctl enable lowdiskcheck.timer
```

