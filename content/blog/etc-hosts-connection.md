---
title: "Changing /etc/hosts based on network connection"
date: 2023-11-22T09:23:09-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

I use my laptop at home, university, and public locations. The IP address I use to connect to a particular resource changes depending on if I'm within the network it's hosted on or a VPN. A common solution is to have a DNS server within the VPN that all clients use. This, however, has a few issues:

- If the client has multiple VPNs connected, only one DNS server can be set.
- There may be more latency using a DNS server within a VPN than using a default one provided by the ISP.
- You may not have permission to host the DNS server within the VPN network.

To address these set of issues, we'll go over how to change `/etc/hosts` on the local client machine depending on which network it's connected to.

In this setup, we'll have a default `/etc/hosts` file. I'll show how to then *swap* it with one for a particular connection. To do this, we need a way for a script to run when NetworkManager connects or disconnects from a network.

Luckily, `NetworkManager-dispatcher` handles this for us. To get a complete understanding on how to write scripts for this, reference

```bash
man 8 networkmanager-dispatcher
```

In essence, scripts within `/etc/NetworkManger/dispatcher.d/` get executed in alphabetical order with two arguments set and a lot of environmental variables.

What we'll care about in our scripts are:

- `$1` the first argument passed to the script is the interface
- `$2` the second argument refers to the *event* being triggered. 
  - Possible options include: pre-up, up, pre-down, down, vpn-up, vpn-pre-up, vpn-pre-down, vpn-down, hostname, dhcp4-change, dhcp6-change, connectivity-change, reapply.
- `$CONNECTION_UUID` refers to a particular connection profile in NetworkManager. This is so we know which `/etc/hosts` file to swap with which connection.

Doing some quick in dirty tests, I found the following events were triggered when connecting to a particular network:

` dhcp4-change -> up -> connectivity-change`

And, the following events were triggered when disconnecting from a particular network:

`connectivity-change -> down`

My first instinct was to use the `connectivity-change` event, however, the `CONNECTION_UUID` variable is not set for those. Instead we'll use the `up/down` events.

For our example, here's what our default `/etc/hosts/` file will look like:

```
127.0.0.1   localhost localhost.localdomain localhost4 localhost4.localdomain4
::1         localhost localhost.localdomain localhost6 localhost6.localdomain6

10.10.10.3  home-server.brandonrozek.com
10.10.10.4  home-desktop.brandonrozek.com
```

When we're connected to my home network, we'll swap my `/etc/hosts/` to look like:

```
127.0.0.1   localhost localhost.localdomain localhost4 localhost4.localdomain4
::1         localhost localhost.localdomain localhost6 localhost6.localdomain6

192.168.0.30  home-server.brandonrozek.com
192.168.0.40  home-desktop.brandonrozek.com
```

The following script we'll store at `/etc/NetworkManager/dispatcher.d/swap_home.sh` which will swap the `/etc/hosts` file with the one stored at `/etc/NetworkManager/hosts.home` when I connect to my home network.

```bash
#!/usr/bin/env bash

interface=$1
event=$2

if [[ $interface != "wlp0s20f3" ]] || [[ $event != "up" ]] then
        exit 0
fi

# This environmental variable is set on UP/DOWN events
if [[ $CONNECTION_UUID != "901a1b68-e622-4be6-a61f-a8dc999212b3" ]] then
        exit 0
fi

cp /etc/NetworkManager/hosts.home /etc/hosts
```

In this script, you might have to replace `wlp0s20f3` to reflect the interface that you're using for connecting to the network. Additionally, you'll have to replace the `CONNECTION_UUID` with the UUID of the connection you're trying to swap under. You can use `nmcli c` to show the UUIDs for each of your network connections.

Similarly, when we disconnect from the network, we'll need to set it back to our default `/etc/hosts` file.

```bash
#!/usr/bin/env bash

interface=$1
event=$2

if [[ $interface != "wlp0s20f3" ]] || [[ $event != "down" ]] then
        exit 0
fi

cp /etc/NetworkManager/hosts.default /etc/hosts
```

