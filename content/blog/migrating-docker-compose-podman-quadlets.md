---
title: "Migrating from Docker Compose for Podman to Quadlets"
date: 2024-05-09T18:53:51-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

Technology never stagnates. There's always people working hard to improve the current status quo. While it might be annoying at times, it does keep life exciting.

The latest change, is that for systems where I use Podman containers, I now no longer use docker-compose but instead rely on Podman Quadlets which are managed by systemd. This means one less dependency on the docker toolchain, and we all accepted the systemd future by now right?

Mo wrote a [blog post](https://mo8it.com/blog/quadlet/) earlier this year outlining how they work. I won't reiterate that great work so I encourage you to check it out. Instead, I'll paste one systemd configuration file of a podman container for future me to easily reference.

Hedgedoc Container file at `/etc/containers/systemd/hedgedoc.container`

```ini
[Container]
ContainerName=hedgedoc
HostName=hedgedoc
Image=lscr.io/linuxserver/hedgedoc:1.9.9
AutoUpdate=registry
Volume=/home/rozek/Volumes/hedgedoc/config:/config
EnvironmentFile=/home/brozek/Volumes/hedgedoc/docker.env
IP=10.77.1.91
Network=rozeknet

[Unit]
Requires=hedgedoc_database.service
After=hedgedoc_database.service

[Service]
Restart=always

[Install]
WantedBy=default.target
```

