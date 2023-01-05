---
title: "Website Status Checking"
date: 2022-09-28T16:05:23-04:00
draft: false 
tags: []
math: false
medium_enabled: true
---

How do I know when my website goes up or down? Recently, I started using a service from [updown.io](https://updown.io) which gives me a status page and notifies me when it goes down.

Q1: Why are you not self-hosting this via say [changedetection.io](https://github.com/dgtlmoon/changedetection.io)?

First, I've never been a big fan of setting up email alerting. It's not because of its technical difficulty, but mostly since I'm lazy. I don't want to have to setup an email address with SMTP access for applications to use. Similar laziness prevents me from creating API tokens for the various chat applications.

There's also the issue of how do I know when my monitoring system is down? I want this to be as hands-off as possible, so regularly checking my self-hosted service to see if its working properly is a no-go.

Q2: Okay, but surely you can download an application locally to check constantly instead?

Indeed! I admit, I haven't fully pursued this option. In regards to mobile, I'm hesitant to download any app that's meant to be consistently on. There's the practical reason of battery performance, as mobile operating systems often freeze applications in its battery optimization. Also, I've never been a fan of having persistent notifications. 

In my quick search, I haven't found an uptime monitor on Linux that doesn't require a whole web application. I was thinking maybe there would a gnome or KDE widget. Ideally it would be a systemd timer or CRON job that would use the notification API when it notices your website is down.

Q3: Can I see your uptime?

Sure! It's shown at [status.brandonrozek.com](https://status.brandonrozek.com). Luckily their service allows for CNAMEs so that I can use my domain name. The CNAME points to page.updown.io and a TXT record on my domain then tells updown to point it to https://updown.io/lbxi

Q4: Anything else?

In addition to a simple UP/DOWN metric. The service checks for TCPv4, TCPv6, and HTTP2 capabilities. I note this because I didn't even notice that I wasn't supporting TCPv6. In a future post, I'll document the changes I made to my setup to enable it.

Also, the service is quite affordable. To check one website every 30 minutes amounts to 2 cents a month. If you want to check it every 15 seconds, then it goes up to a little over $2/month.  

Feel free to get in touch with how you monitor your personal website. I'm curious to see how other people are approaching it.
