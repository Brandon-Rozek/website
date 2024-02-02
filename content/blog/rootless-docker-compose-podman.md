---
date: 2022-01-29 20:21:11-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: d31b7e2a688c
tags:
- Containers
title: Rootless Docker-Compose with Podman
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

You'll need a configuration file `docker-compose.yml` defined. Here is a sample one that spins up an image updating service. Replace `$UID` with your user id which you can get from running `id -u` in the terminal.[^1]

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
      - /var/run/user/$UID/podman/podman.sock:/var/run/docker.sock:ro
    restart: always
```

If you want to add to add more volumes to the container, make sure it has the appropriate SELinux label if
you're using a distribution with it enabled.[^2]

```bash
chcon -t container_file_t -R X
```
where `X` is the volume you wish to mount.

Now we can run `docker-compose`!

```bash
docker-compose ps
```

[^1]: I thank the kind reader for the correction to the volumes declaration.
[^2]: https://bugzilla.redhat.com/show_bug.cgi?id=2125878
