---
title: "Obtaining Valid SSL Certificates within an Internal LAN"
date: 2023-09-18T18:26:12-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

I previously wrote about a quick way to create a [certificate authority for an internal LAN](https://brandonrozek.com/blog/internalca/). This is for scenarios in which we don't want that internal network to have access to the Internet or vice-versa. The main downside of this approach, is that for a computer to trust the SSL certificate created by a machine on that LAN, they need to have the public certificate loaded and trusted on that machine. This can become a pain to manage the larger the internal network grows.

However, if the internal network does have access to the Internet, we can use a different tool. Letsencrypt can issue a valid SSL certificate for your network without being able to directly access your network in question! It is able to do this though the `DNS-01` challenge. 

The way this work is that Letsencrypt asks your client to create a DNS `TXT` entry containing some special token. The client then either manually, manually with [hooks](https://certbot.eff.org/docs/using.html#hooks), or via a [plugin](https://community.letsencrypt.org/t/dns-providers-who-easily-integrate-with-lets-encrypt-dns-validation/86438) edits the zone file on the DNS nameserver to add that entry. The Letsencrypt server then only needs to access that DNS nameserver in order to verify that you own the domain; Issuing your certificate upon success.

This is an example on how to get a certificate for an example internal domain `insiderexample.org` using the Linode DNS provider.

```bash
certbot certonly \
  --dns-linode \
  --dns-linode-credentials ~/.secrets/certbot/linode.ini \
  -d insiderexample.org
```

