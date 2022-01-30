---
title: "Rootless Docker-Compose with Podman"
date: 2022-01-29T20:21:11-05:00
draft: false
tags: ["Containers"]
math: false
---

One of the benefits of Podman over Docker is that it can run daemon-less and without root. However, `docker-compose` is by far my favorite way to create and maintain containers. Luckily, the Podman folks emulated the Docker CLI so that `docker-compose` works well with Podman!

To install:

```bash
sudo dnf install -y podman podman-docker docker-compose
```

We can then emulate the docker socket rootless with the following commands:

```bash
systemctl --user enable podman.socket
systemctl --user start podman.socket
```

At this point, we'll want to see if the daemon acts as expected

```bash
curl -H "Content-Type: application/json" \
	--unix-socket /var/run/user/$UID/podman/podman.sock \
    http://localhost/_ping
```

This should return `OK`. We then need to create an environmental variable to tell docker compose where the emulated docker socket lives.

```bash
export DOCKER_HOST=unix:///run/user/$UID/podman/podman.sock
```

To have this environmental variable persistent across reboots, add the above line to the user's `.bash_profile`.

You'll need a configuration file `docker-compose.yml` defined. Here is a sample one that spins up an image updating service.

```yaml
version: "3.3"

services:
  watchtower:
    image: docker.io/containrrr/watchtower 
    container_name: watchtower
    hostname: watchtower
    environment:
      PUID: 1000
      PGID: 1000
      TZ: US/Eastern
    volumes:
      - /var/run/podman/podman.sock:/var/run/docker.sock:ro
    restart: always
```

Now we can run `docker-compose`!

```bash
docker-compose ps
```
