---
title: "Temporarily Resolving Hostnames"
date: 2020-01-04T21:26:16-05:00
draft: false
images: []
---

Let's say that we're testing a webserver where the pages served depended on a domain that you don't own. The most common way I know to test this is to modify your `/etc/hosts` file to contain the hostname and ip address you want to map it to.

```
192.168.1.2   custom.domain
```

I've recently discovered that the command line utility `curl` has a quick and easy option to forge the hostname of a request.

```bash
curl --resolve domain:port:ipaddr url
```

There are also browser extensions that you can use such as [LiveHosts](https://github.com/Aioros/livehosts) to get around this as well. This post isn't entirely useful when talking about permanent services.

If this is going to be a publicly facing service, then you should just set the records of your domain name to point to the server.

If it's a non-public routable service, then perhaps try looking into setting up your own private [dns server](https://brandonrozek.com/blog/coredns/).