---
date: 2021-06-18 23:38:43
draft: false
medium_enabled: true
medium_post_id: 790558856bee
tags:
- Networking
title: Forward Packets with Socat
---

I've written about relaying TCP traffic using [SSH port forwarding](/blog/sshlocalportforwarding/). Though sometimes you don't require the authenticity and encryption of SSH or want to use another protocol such as UDP. That's where `socat` comes in.

The following will listen to TCP traffic on port 8001 and redirect it to TCP localhost:8000

```bash
socat tcp-listen:8001,reuseaddr,fork tcp:localhost:8000
```

This will listen UDP on port 4009 and forward it to UDP localhost:4010

```bash
socat udp-listen:4009,reuseaddr,fork udp:localhost:4010
```