---
title: "OpenVPN Container"
date: 2020-04-30T23:20:49-04:00
draft: false
tags: ["Containers"]
medium_enabled: true
---

Instead of configuring multiple containers to use a VPN, we can setup a VPN container and route the other containers traffic through this container. This post will outline how to do that with [dperson's OpenVPN Container](https://github.com/dperson/openvpn-client).

I'm a huge fan of docker-compose, so here we go:

```yaml
version: "3.3"
services:
  openvpn-client:
    image: dperson/openvpn-client
    cap_add:
      - net_admin
    security_opt:
      - label:disable
    container_name: openvpn-client
    hostname: openvpn-client
    environment:
      - PUID=1000
      - PGID=1000
    volumes:
      - /dev/net:/dev/net:z
      - /volumes/openvpn-client/vpn/:/vpn
    restart: always
```

The `net_admin` capability according to the documentation "perform various network-related operations".  This would make sense since an additional network interface is configured for a VPN connection. The `label:disable` definition is to disable label confinement.

In this setup, you will need to put the `.ovpn` profile that you wish to connect to under the `/volumes/openvpn-client/vpn/` directory. 

## (Optional) Username/Password Setup
In the event you need a username and password to connect, create a file called `pass.txt` in the same directory as your ovpn profile. The file `pass.txt` will contain the username in the first line and the password in the second line. Then in your ovpn profile make sure you have a line that says `auth-user-pass pass.txt`.

## Routing Traffic through VPN

Let's say your ISP throttles torrent connections and you want to route your `qBittorrent` container so that you can download Linux distributions faster. Here's how you can define it in the docker-compose file.

```yaml
qbittorrent:
  image: linuxserver/qbittorrent
  container_name: qbittorrent
  environment:
    - PUID=1000
    - PGID=1000
    - UMASK_SET=022
    - WEBUI_PORT=8000
  volumes:
    - /volumes/qbittorrent/config:/config
    - /volumes/qbittorrent/downloads:/downloads
  network_mode: service:openvpn-client
  restart: always
```

## Network Workarounds

Sadly as of the time of writing, routing a container's traffic makes it lose its ability to belong to a network. I knocked into this when I tried accessing the qBittorrent API. So for the sake of example, if you want to connect to qbittorrent, you need to route the traffic to the openvpn-client container at port 8000 which we specified earlier to be the webui port of qbittorrent.
