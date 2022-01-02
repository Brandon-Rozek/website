---
title: "Docker Macvlan Networks"
date: 2020-05-26T01:01:43-04:00
draft: false
tags: ["Containers"]
---

It is useful to have some docker containers live in the same network as your host machine. We can accomplish this by creating a new MAC address for the container and using the `macvlan` driver. Here is example Docker Compose configuration

```yml
services:  
  nginx:
    image: linuxserver/nginx
    container_name: nginx
    hostname: nginx
    # Randomized MAC address
    mac_address: 4E:64:A4:60:8D:0E
    environment:
      PUID: 1000
      PGID: 1000
    volumes:
      - /etc/nginx:/config/nginx
    restart: always
    ports:
      - 80/tcp
      - 443/udp
    networks:
      macvlan_network:
        # Static IP for host network
        ipv4_address: 192.168.0.10
      # Allow access to nginx container in default docker network
      default: 

networks:
  macvlan_network:
    driver: macvlan
    driver_opts:
      # Obtain device name by looking at `ip addr`
      parent: eno1
    ipam:
      config:
        - subnet: 192.168.0.0/24
```

