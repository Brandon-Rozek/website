---
title: "coredns"
date: 2019-12-13T02:00:29-05:00
draft: false 
tags: [ "Linux", "Networking", "Containers" ]
---

Domain names are the easiest way for a reverse proxy to split up services in a homelab. Since I'm going full docker-compose in my homelab, I decided to use `coredns`.

The server I'm hosting my services on runs Ubuntu 18.04 at the time of writing. This verison of Ubuntu comes packaged with their own DNS resolver `systemd-resolved` which runs on port 53. Therefore in order to stop this, we need to edit `/etc/systemd/resolved.conf`:

```ini
DNS=127.0.0.1
FallbackDNS=
Domains=~.
DNSStubListener=no
```
You might be wondering about the `~.` option in Domains. From the [Arch Wiki](https://wiki.archlinux.org/index.php/Systemd-resolved), "Without the `Domains=~.` option, systemd-resolved might use the per-link DNS servers."

You also need to remove the already existing `/etc/resolv.conf` file.
```bash
sudo rm /etc/resolv.conf
```

Now to setup `coredns` I used the following docker-compose snippet:
```yaml
coredns:
  image: coredns/coredns
  command: -conf coredns-config/Corefile
  ports:
    - 53:53/udp
  volumes:
    - /Volumes/coredns/coredns-config:/coredns-config/
```
Noticed that I mounted the configuration directory in a volume. `coredns` is managed by a configuration file. This would be located under `/Volumes/coredns/coredns-config/Corefile` in the host system.

Let's say we own the domain example.com and want subdomains of that to point to different to our server. To do that, we need to define a zonefile for that domain name. We will save that under `/Volumes/coredns/coredns-config/homelab.db` in our host system. Every other domain we will either pass to a public DNS server like Google's `8.8.8.8` or you can even use a PiHole.

Example Corefile:
```
example.com:53 {
    file /coredns-config/homelab.db
    log
    errors
}

.:53 {
    log
    errors
    forward . 8.8.8.8
    cache
}
```
I do recommend that whatever domain you do use for your homelab is one you own. Otherwise you might name conflict with a public service that you would want to access in the future.

The `cache` directive will cache results from the other DNS provider for quicker delivery at a later point.

The zonefile `homelab.db` could look like the following:
```
$TTL    3600
$ORIGIN example.com.
@                    IN  SOA   ns.example.com. contact.example.com. (
                                               2019121301 ; serial
                                               1d ; refresh
                                               2h ; retry
                                               4w ; expire
                                               1h ; nxdomain ttl
                                              )
                     IN  NS  ns.example.com.
@                    IN  A   192.168.1.10
*                    IN  A   192.168.1.10
@                    IN  A   10.10.100.10
*                    IN  A   10.10.100.10
```

In the zone file, `@` means whatever the value of `$ORIGIN` is and `*` is a wildcard meaning any subdomain. You can assign a local LAN address first and then a VPN ip address if you have one set up to access services remotely.

The serial number needs only to be unique across SOA entries, and is conventionally the date and hour in which the entry was modified.

I have this setup since all my services are on one physical machine. If you want to split it up through many different machines, specify it by adding the subdomains in place of the `*` or `@`.

After the `Corefile` and `homelab.db` are made, the DNS server is all ready to be up and running. Just execute `docker-compose up -d coredns` and the DNS server will start happily responding to requests.

A good way to verify it works is to request an `A` record from your site and an external site.

```bash
dig @serverip example.com A
dig @serverip google.com A
```

