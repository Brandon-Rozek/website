---
title: "Non-Root Systemd Scripts"
date: 2022-03-15T23:55:19-04:00
draft: false
tags: ["Linux"]
math: false
medium_enabled: true
---

I know of two ways to run systemd services not as root. They both have their pros and cons associated with them.

### 1. Define User/Group

The first method is one I have done before in my [docker-compose startup post](/blog/composesystemd/). It involves adding the `User` and `Group` fields to the `Service` component of the Systemd unit file.

Filename: `/etc/systemd/system/docker-compose.service`

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

You can then start and enable it at boot with

```bash
sudo systemctl start docker-compose
sudo systemctl enable docker-compose
```

### 2. User-Level Systemd with Lingering Users

An alternative is to have the service file in the user's systemd config directory and add the `--user` flag during the systemd call.

Filename: `/home/brandonrozek/.config/systemd/user/docker-compose.service`

```ini
[Unit]
Description=Docker Compose Application Service
Requires=docker.service
After=docker.service

[Service]
Type=oneshot
RemainAfterExit=yes
WorkingDirectory=/home/brandonrozek/docker/
ExecStart=/usr/bin/docker-compose up -d
ExecStop=/usr/bin/docker-compose down
TimeoutStartSec=0

[Install]
WantedBy=multi-user.target
```

To start and enable:

```bash
systemctl --user start docker-compose
systemctl --user enable docker-compose
```

An issue with this approach as it is right now is that the service will only run while the user is logged in. If you want the service to run despite whether or not the user is logged in, then you'll need to mark the user as lingering.

```bash
sudo loginctl enable-linger $USER
```

You can check if a user already has that property:

```bash
sudo loginctl show-user $USER --property Linger
```

You can even list all users with the linger property:

```bash
ls /var/lib/systemd/linger
```

To disable that property:

```bash
sudo loginctl disable-linger $USER
```

Now what does linger even do?

From [FreeDesktop](https://www.freedesktop.org/software/systemd/man/loginctl.html), if linger is enabled for a sepcific user, then a user manager is spawned for that user at boot which handles the user's services and is kept around even after logouts. If  linger is not enabled, then a user's services will not start at boot and will stop after the user has no sessions running.

### Pros/Cons

For a multi-user system, one can argue that linger is not a good property to have because users can then have a lot of processes spawned and persistent even if they are not using the system. In that case, having an admin individually add systemd unit files using the first approach makes sense.

The second approach has the benefit that the admin only has to set the linger property of the user once, and then the user can create as many systemd unit services as they'd like.
