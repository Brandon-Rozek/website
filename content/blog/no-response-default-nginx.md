---
title: "No Response Default in Nginx"
date: 2024-01-01T17:21:51-05:00
draft: false
tags:
    - Nginx
math: false
medium_enabled: false
---

> Welcome to nginx!

After installing `nginx` fresh on a server, this classic quote is part of a welcome page that is automatically setup within a default configuration file. On Redhat-based systems this lives under `/etc/nginx/conf.d` and for Ubuntu-based ones under `/etc/nginx/sites-available/`.

This page mostly exists to make sure that everything is squared away after installation. However, how can we get rid of the page once we have all the site configurations loaded?

We'll show how to get rid of the default welcome page by changing the `default.conf` file.

When you type in `https://brandonrozek.com` in your web browser, your system will first (1) look up the IP (at the time of writing it's `173.255.230.230`) and then (2) send a HTTP request with the header including `Host('brandonrozek.com')`. It's the `Host` header that lets `nginx` know which content to serve.

So if `nginx` comes across a `Host` header that doesn't have a specified configuration for, then it follows some default behavior. This is described under the configuration file with the host `default_server`.

One good default behavior is to not bother responding to the request. For this purpose, the best HTTP response code is `444` No Response.

The `nginx` configuration on the HTTP side looks like the following:

```nginx
server {
    listen 80 default_server;
    listen [::]:80;

    server_name _;
    return 444;
}
```

Under standard HTTPS, a SSL handshake occurs. Though this seems pointless if all we're doing is returning nothing. Therefore, we can reject the handshake as well.

```nginx
server {
    listen 443 ssl;
    listen [::]:443 ssl;
    http2 on;
    ssl_reject_handshake on;

    server_name _;
    return 444;
}
```

All together, a modified `default.conf` looks like:

```nginx
server {
    listen 80 default_server;
    listen [::]:80;

    server_name _;
    return 444;
}

server {
    listen 443 ssl;
    listen [::]:443 ssl;
    http2 on;
    ssl_reject_handshake on;

    server_name _;
    return 444;
}
```

