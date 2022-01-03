---
title: "SOCKS5 Proxy"
date: 2022-01-03T10:41:09-05:00
draft: false
tags: ["Networking", "SSH"]
math: false
---

A SOCKS5 proxy allows you to have network traffic as if it was coming from the proxy server as opposed to your local client. You can easily set it up using SSH from your local machine.

```bash
ssh -D 1337 -N user@remotehost
```

The above command opens the port 1337 on localhost and redirects traffic from that port over the SSH connection to the remote machine.

On the client computer, you can then go to your browser settings and specify `localhost:1337` as a SOCKS5 proxy. Some commands allow you to specify a proxy in their flags. For example:

```bash
curl --proxy socks5h://localhost:1337 https://brandonrozek.com/
```

Not all commands make this easy however, which is where `proxychains` comes in. It allows you to route traffic from a specified subcommand over a proxy. For example:

```bash
proxychains curl https://brandonrozek.com
```

To do this you will need proxychains installed. On Ubuntu, the package is called `proxychains4`. Then you'll need to edit the bottom of `/etc/proxychains4.conf` to contain the following line:

```
socks5  127.0.0.1  1337
```

