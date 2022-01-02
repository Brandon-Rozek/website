---
title: "Wildcard Domains in PiHole"
date: 2020-05-25T23:26:00-04:00
draft: false
tags: ["Networking"]
---

As of this time of writing, the current version of PiHole (5.0) supports adding custom DNS records, but not wildcard records. This makes it annoying if you run a bunch of different services within your LAN following a certain pattern. 

Though since PiHole runs on top of `dnsmasq` it is easy to add an additional configuration file to point a domain containing `example.com` to a specific ip.

If you look in `/etc/dnsmasq.d/` there are the files `01-pihole.conf` and `02-pihole-dhcp.conf`. For our wildcard record, we're going to add a new file `03-custom-dns.conf`. Let's have an example where we want to map `example.com` and `*.example.com` to `192.168.0.10`.

```
address=/example.com/192.168.0.10
```

Once you save, restart the container or box and you will then have the wildcard record!