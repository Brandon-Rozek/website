---
title: "Obtaining a IPv6 Address via Hurricane Electric's Tunnel Broker Service"
date: 2023-10-09T22:31:10-04:00
draft: false 
tags: []
math: false
medium_enabled: false
---

Lately, I have come across a virtual private server that only has a IPv4 address and not a IPv6 address. Since all regional Internet registries have [exhausted their IPv4 address pools since 2019](https://en.wikipedia.org/wiki/IPv4_address_exhaustion), I wanted to find a way to route IPv6 traffic to that server.

Luckily, Hurricane Electric provides a free IPv6 tunnel broker service. The [Arch Linux Wiki](https://wiki.archlinux.org/title/IPv6_tunnel_broker_setup) has a great guide on how to set it up. This post will start off with setting up the service, and we'll discuss a couple bits of consideration we need to take to get IPv6 traffic to a webserver running in a docker/podman container.

Hurricane Electric is a Tier 2 Internet service provider. This means that they [peer](https://en.wikipedia.org/wiki/Peering) with other Internet service providers to route network traffic with. Since at [least 2010](https://forums.he.net/index.php?topic=783.0), Hurricane Electric has offered a [free IPv6 tunnel](https://www.tunnelbroker.net/).   This gives me confidence that they should at least continue to offer this service in the near future. In order to route IPv6 traffic to your IPv4 server, they make use of the the [6in4 tunneling protocol](https://en.wikipedia.org/wiki/6in4). This encapsulates the IPv6 packet with a IPv4 header. 

To get setup, create on account on https://tunnelbroker.net. After verifying your email, login and click on "Create Regular Tunnel". From there it will ask you for the IPv4 address of your server. Insert that and then click the tunnel server that is the closest geographically to where the server is located.

Once the tunnel is created, you'll need to take note of four addresses within the "IPv6 Tunnel Endpoints" section:

- Server IPv4 Address
- Server IPv6 Address
- Client IPv4 Address
- Client IPv6 Address

In terms of configuring the networking on the server, I found the systemd script on the Arch Wiki the most straightforward setup. Within `/etc/systemd/system/he-ipv6.service`

```ini
[Unit]
Description=he.net IPv6 tunnel
After=network.target

[Service]
Type=oneshot
RemainAfterExit=yes
ExecStart=/usr/bin/ip tunnel add he-ipv6 mode sit remote server_IPv4_address local client_IPv4_address ttl 255
ExecStart=/usr/bin/ip link set he-ipv6 up mtu 1480
ExecStart=/usr/bin/ip addr add client_IPv6_address dev he-ipv6
ExecStart=/usr/bin/ip -6 route add ::/0 dev he-ipv6
ExecStop=/usr/bin/ip -6 route del ::/0 dev he-ipv6
ExecStop=/usr/bin/ip link set he-ipv6 down
ExecStop=/usr/bin/ip tunnel del he-ipv6

[Install]
WantedBy=multi-user.target
```

Then enable/start the service with:

```bash
sudo systemctl enable --now he-ipv6.service
```

With this, your server should now be IPv6 routable. You can test this by trying to ping your server from another IPv6 enabled device.

```bash
ping client_ipv6_address
```

If that works, next you'll have to make sure that [docker/podman and nginx are configured to accept TCPv6 traffic](https://brandonrozek.com/blog/podman-nginx-tcpv6-http2-ready/). Finally, since the tunnel is on a different network interface, you may need to allow routing at the firewall level.

For example, to allow from traffic between the podman and tunnel interfaces:

```bash
sudo ufw route allow in on he-ipv6 out on podman1
sudo ufw route allow in on podman1 out on he-ipv6
```

