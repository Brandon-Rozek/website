---
title: "Ensuring Docker Compose Startup with Systemd"
date: 2019-12-16T20:57:36-05:00
draft: false 
tags: [ "Linux", "Containers" ]
---

I've been having trouble getting some docker containers such as `nginx` to start automatically on bootup, even with the `restart: always` flag.

To compensate, I wrote a small systemd script and enabled it on startup.

`/etc/systemd/system/docker-compose.service`

```ini
[Unit]
Description=Docker Compose Application Service
Requires=docker.service
After=docker.service

[Service]
Type=oneshot
User=brandonrozek
Group=brandonrozek
RemainAfterExit=yes
WorkingDirectory=/home/brandonrozek/docker/
ExecStart=/usr/bin/docker-compose up -d
ExecStop=/usr/bin/docker-compose down
TimeoutStartSec=0

[Install]
WantedBy=multi-user.target

```

To enable on startup

```bash
sudo systemctl enable docker-compose
```

To start now

```bash
sudo systemctl start docker-compose
```

