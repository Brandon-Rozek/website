---
title: "Wireguard VPN"
date: 2019-11-20T20:09:59-05:00
draft: false
---

Having some sort of VPN solution has always been a necessity for me. Whether it's back in the day where LAN games where the rage and I wanted to play it with my distant friends, or nowadays when I need to be able to access my Desktop running simulations behind my home LAN.

This blog post is going to describe how I settled on Wireguard VPN as my preferred solution and how I use it to create a small secured network.

Keep note that I am not talking about a VPN that masks your internet traffic. For that, look up a VPN provider such as Private Internet Access or ProtonVPN.

## About Wireguard

Wireguard is a point-to-point protocol. This means that you will be exchanging public and private keys between two clients and only those two clients will communicate with one another. 

In a way this makes it a lot simpler than other VPN solutions like OpenVPN where you have to set up a key server. That doesn't mean, however, that we cannot build upon this concept to create a secure network.

Now in order to create this network, we'll need at least one publicly accessible through the Internet computer. I use a VPS instance on [DigitalOcean](https://www.digitalocean.com/) to act as my *server*.

## Key Generation

First you'll want to get [Wireguard installed](https://www.wireguard.com/install/), and then create public-private keys for both the *server* and the *client* computers.

**On each machine:**

```bash
cd /etc/wireguard
sudo umask 077
sudo wg genkey | tee privatekey | wg pubkey > publickey
```

**On the server:**

Edit `/etc/wireguard/wg0.conf`

```yaml
[Interface]
Address = 10.10.100.1/24
SaveConfig = false
ListenPort = 51826
PrivateKey = <server_private_key>

[Peer]
PublicKey = <client1_public_key>
AllowedIPs = 10.10.100.2/32

[Peer]
PublicKey = <client2_public_key>
AllowedIPs = 10.10.100.3/32
```

You might be wondering why we have `/24` in the Address field but `/32` in the AllowedIPs field.

This is because we want our address to be in the `/24` subnet, but we only want that specific IP to be able to connect via that specific public key.

Warning: Make sure you have 51826 open on your firewall.

Now to have your server route traffic between the different clients connected to it, you need to enable IPv4 forwarding.

*For current session:*

```bash
sysctl -w net.ipv4.ip_forward=1
```

*For persistence across reboots:*

Edit `/etc/sysctl.d/99-sysctl.conf` to make sure `net.ipv4.ip_forward=1`

**On the client machines:**

Edit `/etc/wireguard/wg0.conf`

```yaml
[Interface]
Address = 10.10.100.x/32
PrivateKey = <client_private_key>
PostUp = ping -c1 10.10.100.1
DNS = 10.10.100.y # Include only if relevant

[Peer]
PublicKey = <server_public_key>
Endpoint = public_ip_or_domain:51826
AllowedIPs = 10.10.100.0/24
PersistentKeepalive = 21
```

Replace `x` with a unique value per client. This configuration file has the client establish a connection to the server, send a packet via ping to initiate the connection and then try to persistently keep it alive.

The DNS server is helpful if you have a DNS server running in that private network to access local resources. If you don't have an existing DNS server in the network, do not include that line. Also if you receive any errors in the future, you might need to make sure `resolvconf` is a command on your system.

**On all machines:**

Have the wireguard service start at boot

```bash
sudo systemctl enable wg-quick@wg0
sudo systemctl start wg-quick@wg0
```

And enjoy a fully secure routable network!

