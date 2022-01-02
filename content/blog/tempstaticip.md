---
title: "Temporary Static IP"
date: 2020-01-20T21:36:37-05:00
draft: false
tags: [ "Linux", "Networking" ]
---

I've learned that the fastest way to transfer files is via Ethernet. Now the easiest way to transfer via Ethernet is for both computers to be on the same local area network. However, if needed, an Ethernet cable can used between two computers. 

In order for both the computers to recognize each other, they need to be on the same subnet.

First on both computers, find out which network device is your Ethernet.

```bash
ip addr show
```

Then on both computers assign an unique static ip address,

```bash
sudo ip addr add 10.1.1.2/24 dev en0
```

In this example,

- `10.1.1` is the subnet that the computer is assigned to.
- `2` will denote the unique ip address
- `/24` defines the first three digits as the subnet
- `en0` is the example network device that's the Ethernet.

Once that's in place you should be able to `ping` and `rsync` between the two computers!

*If you run into issues, it might be a firewall problem...*

To remove the static ip assignment, replace `add` with `del`
```bash
sudo ip addr del 10.1.1.2/24 dev en0
```

