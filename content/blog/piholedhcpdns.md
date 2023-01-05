---
title: "Configuring DHCP DNS in Pihole"
date: 2020-05-25T23:36:51-04:00
draft: false
tags: ["Networking"]
medium_enabled: true
---

There are two scenarios I can imagine in where you want to configure the DNS set by PiHole

1. You have multiple PiHole's in your LAN
2. You have a multi-layer DNS setup

In either case, we can utilize `dnsmasq` configurations in order to set the DNS option.  You should already notice `01-pihole.conf` and `02-pihole-dhcp.conf` in `/etc/dnsmasq.d`, we'll need to create one that is numbered `03-*` or greater. I'll use `/etc/dnsmasq.d/03-dhcp-dns.conf` as my example.

To set the initial DNS server to be from the router.

```
dhcp-option=6,192.168.0.1
```

To set multiple DNS servers

```
dhcp-option=6,192.168.0.2,192.168.0.3
```

