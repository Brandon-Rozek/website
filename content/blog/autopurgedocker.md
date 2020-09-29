---
title: "Auto Purge Old Docker Images"
date: 2020-09-28T23:30:22-04:00
draft: false
tags: []
---

I use [Watchtower](https://github.com/containrrr/watchtower) to automatically update the docker images I use. After leaving it for several months, I've realized that I have been storing over 100GB of old docker images. I needed a way to automatically purge  old images and [Systemd Timers](https://opensource.com/article/20/7/systemd-timers) is the solution.

First it's useful to know the docker command that purges unused images that are older than 24 hours old.

```bash
docker image prune -fa --filter "until=24h"
```

Then we can create a oneshot service file that will describe its dependencies and descriptions for Systemd to manage. This file is `/etc/systemd/system/docker-purge.service`.

```yml
[Unit]
Description=Purge Docker Images Older than 24 Hours
Requires=docker.service
Wants=docker-purge.timer

[Service]
Type=oneshot
ExecStart=/usr/bin/docker image prune -fa --filter "until=24h"

[Install]
WantedBy=multi-user.target
```

Now we can create the systemd timer that will hook to this service. This is `/etc/systemd/system/docker-purge.timer`.

```yaml
[Unit]
Description=Purge Docker Images Older than 24 Hours
Requires=docker-purge.service

[Timer]
Unit=docker-purge.service
OnCalendar=*-*-* 00:00:00
AccuracySec=24h

[Install]
WantedBy=timers.target
```

This tells Systemd to run the service every day if enabled/started, though not necessarily at midnight. Systemd will schedule a time to run the service within the `AccuracySec` parameter. That is, it will schedule a time to run sometime everyday. 

Finally, let's enable and start the timer.

```bash
sudo systemctl enable docker-purge
sudo systemctl start docker-purge
```

We can check the time that docker-purge is scheduled to run next by asking Systemd to list its timers.

```bash
systemctl list-timers
```

If you want to play around with the `OnCalendar` parameter.  A useful command is

```bash
systmed-analyze calendar --iterations=$N "$TIME"
```

Where you replace `$N` with an integer, and `$TIME` with your sample time string.