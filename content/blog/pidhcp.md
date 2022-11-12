---
title: "DHCP for Raspberry Pi"
date: 2021-02-15T22:46:21-05:00
draft: false
tags: ["Networking"]
---

Recently I ran across the use case where I needed a Raspberry Pi to be connected to the Internet via a WiFI connection, while also providing DHCP leases through an Ethernet connection. I couldn't find a great way to achieve this with `dhcpcd` so instead I grabbed a tool that I'm more familiar with `dnsmasq`. 

Before we begin, we need to setup a static IP for the Ethernet interface (`eth0`). Since the Ethernet interface will not be connected to the Internet, there's no need to worry about a lot of the usual fields.

In `/etc/dhcpcd.conf`

```
interface eth0
fallback nodhcp

profile nodhcp
static ip_address=192.168.2.1/24
```

Below is the config for `dnsmasq` which lives in `/etc/dnsmasq.conf`. It essentially tells it to only serve DHCP leases on the Ethernet connection of the Raspberry Pi. The addresses it'll lease out according to the config below is between 192.168.0.50-192.168.0.150 and is leased for 12 hours.

```
# Configuration file for dnsmasq.
#
# Format is one option per line, legal options are the same
# as the long options legal on the command line. See
# "/usr/sbin/dnsmasq --help" or "man 8 dnsmasq" for details.

# Listen on this specific port instead of the standard DNS port
# (53). Setting this to zero completely disables DNS function,
# leaving only DHCP and/or TFTP.
port=0

# If you want dnsmasq to listen for DHCP and DNS requests only on
# specified interfaces (and the loopback) give the name of the
# interface (eg eth0) here.
# Repeat the line for more than one interface.
interface=eth0
# Or you can specify which interface _not_ to listen on
#except-interface=
# Or which to listen on by address (remember to include 127.0.0.1 if
# you use this.)
#listen-address=

# Uncomment this to enable the integrated DHCP server, you need
# to supply the range of addresses available for lease and optionally
# a lease time. If you have more than one network, you will need to
# repeat this for each network on which you want to supply DHCP
# service.
dhcp-range=192.168.0.50,192.168.0.150,12h

# Enable DHCPv6. Note that the prefix-length does not need to be specified
# and defaults to 64 if missing/
#dhcp-range=1234::2, 1234::500, 64, 12h
```

