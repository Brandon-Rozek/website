---
title: "Ping Discovery"
date: 2020-02-02T22:21:30-05:00
draft: false
images: []
---

Plugging in a device into a network with DHCP will often result in you not knowing what the ip is. If you don't have easy access to the DHCP server, then one way to see what ip addresses are on the network is to do a ping scan. 

Please make sure that this is either your home network or that you have permission before doing a scan. 

First you'll need to know the subnet that you are working off of. 

```bash
ip addr show
```

You might get something like the following

```
2: wlan0: <BROADCAST,MULTICAST,UP> mtu 1500 qdisc noqueue state UP group default qlen 1000
    link/ether 96:25:48:13:62:02 brd ff:ff:ff:ff:ff:ff
    inet 192.168.0.5/24 brd 192.168.0.255 scope global dynamic noprefixroute wlan0
```

Right after `inet` note the `192.168.0.5/24`. The `/24` subnet means that the last number changes. We can replace our last number then with zero and start the ping scan.

```bash
nmap -sn 192.168.0.0/24
```

