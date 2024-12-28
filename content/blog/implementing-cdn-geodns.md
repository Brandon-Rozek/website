---
title: "Rolling out my own CDN with GeoDNS"
date: 2024-12-28T07:11:16-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

I noticed when looking at my [monitoring](https://brandonrozek.com/blog/website-status-checking/) that accessing my website from Asia takes almost a full second to load.

![](/files/images/blog/photo_2024-12-25_22-16-17.jpg)

I apologize to all my visitors in that segment of the green orb.  Please do write to me to tell me you exist though! I'm always happy to hear from readers of my blog.

> Why don't you use Cloudflare?

You see friend, I believe in a decentralized web. I want to do my part in not contributing to the monopoly.

Also, I'm not a huge fan of how most CDNs work. I don't want to have my DNS tied to a CDN provider.

This gets me thinking, can I roll out my own CDN? It turns out we can! For the purposes of this personal website, we don't need servers in every country in the globe.

The Internet as we know it, is enabled through many undersea cables. Looking at the [cable map](https://www.submarinecablemap.com/) and the performance timings I have, if I stick a server in Singapore, it should help bring down the load times in Japan and Austrialia as well.

My website is entirely static. This makes keeping everything in sync simple. I only need to make sure that I have a copy of my website on both servers.

Luckily, I was able to snag a VPS in Singapore from [GreenCloud](https://greencloudvps.com/) for only $22/year during Black Friday.  In New York, at the time of writing I'm using [EasyVM](https://easyvm.net/).

Now both servers have `nginx` installed and have the files needed to serve my website to visitors. However, if me in New York tries to connect to a server in Singapore, then I'll be the one waiting for 874ms!

This is where GeoDNS comes in. The DNS server analyzes the IP address of the visitor requesting my websites IP and returns the server that it thinks is the closest!

Not every DNS provider has this feature. At the time of writing, I'm using [Bunny DNS](https://bunny.net/dns/). The first million queries is free, and then it's $0.30 for every million after that. For the month of December, Bunny has responded to 1,166,405 queries for my domain which luckily doesn't break the bank for me.

In the DNS zone, I specify the IP addresses of the two servers and include the GPS coordinates of where they sit. If you don't know that information, you can use a website like [ipinfo.io](https://ipinfo.io/) to find out.

![](/files/images/blog/202412252243.png)

With my extra server and GeoDNS set up, I now have load times under 350ms in all the regions my monitoring service checks!

![](/files/images/blog/202412252248.png)
