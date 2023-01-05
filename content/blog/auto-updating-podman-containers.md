---
title: "Automatically Updating Podman Containers"
date: 2022-05-15T22:20:47-04:00
draft: false
tags: ["Linux", "Containers"]
math: false
medium_enabled: true
---

Recently, I have been  [transitioning to Podman](/blog/rootless-docker-compose-podman)  for running my container infrastructure. In the process, I brought over Watchtower which I have previously used for auto-updating docker containers. Before doing so, I didn't check its [compatibility](https://github.com/containrrr/watchtower/issues/1060) (whoops) and found a few of my containers would every other week or so not come back up.

I then remembered that I restart my server for general system updates almost every day. What if I perform the podman container updates on start up? After modiyfing my systemd service to include an extra field called `ExecStartPre` and removing Watchtower, I found no more missing containers! The field `ExecStartPre` performs a pull (update) before starting up the containers via `ExecStart`.

```ini
[Unit]
Description=Docker Compose Application Service
Requires=network.target podman.socket
After=network.target podman.socket

[Service]
Type=oneshot
RemainAfterExit=yes
WorkingDirectory=/home/brandonrozek
ExecStartPre=/usr/bin/docker-compose pull
ExecStart=/usr/bin/docker-compose up -d --force-recreate
ExecStop=/usr/bin/docker-compose down
TimeoutStartSec=0

[Install]
WantedBy=multi-user.target
```

