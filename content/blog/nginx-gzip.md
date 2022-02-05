---
title: "Reducing Network Bandwidth in Nginx with Gzip"
date: 2022-02-04T20:06:50-05:00
draft: false
tags: []
math: false
---

Browsers that support gzip compression send the header `Accept-Encoding: gzip` in its request and if the webserver supports gzip, then it can send the website data back compressed. Though recently I learned that this isn't setup by default in `nginx`! This post will go over the configuration you'll need to add to `/etc/nginx/nginx.conf` in order to support `gzip` compression. From my experience, enabling `gzip` compression reduced network traffic by 1/4.

Inside of the `server {}` block in `/etc/nginx/nginx.conf` add the following lines:

```nginx
gzip on;
gzip_disable "msie6";

gzip_vary on;
gzip_proxied no-cache no-store private expired auth;
gzip_comp_level 6;
gzip_buffers 16 8k;
gzip_http_version 1.1;
gzip_min_length 1024;
gzip_types
	application/atom+xml
	application/geo+json
    application/javascript
    application/x-javascript
    application/json
    application/ld+json
    application/manifest+json
    application/rdf+xml
    application/rss+xml
    application/xhtml+xml
    application/xml
    font/eot
    font/otf
    font/ttf
    image/svg+xml
    text/css
    text/javascript
    text/plain
    text/xml;
```

What each of the commands do:

| Command             | Description                                                  |
| ------------------- | ------------------------------------------------------------ |
| `gzip_disable`      | Disables gzipping of responses for requests with “User-Agent” header fields matching any of the specified regular expressions. |
| `gzip_vary`         | Enables or disables inserting the “Vary: Accept-Encoding” response header field if the directives [gzip](https://nginx.org/en/docs/http/ngx_http_gzip_module.html#gzip), [gzip_static](https://nginx.org/en/docs/http/ngx_http_gzip_static_module.html#gzip_static), or [gunzip](https://nginx.org/en/docs/http/ngx_http_gunzip_module.html#gunzip) are active. |
| `gzip_proxied`      | Enables or disables gzipping of responses for proxied requests depending on the request and response. The fact that the request is proxied is determined by the presence of the “Via” request header field. |
| `gzip_comp_level`   | Sets a gzip compression `*level*` of a response. Acceptable values are in the range from 1 to 9. |
| `gzip_buffers`      | Sets the `*number*` and `*size*` of buffers used to compress a response. By default, the buffer size is equal to one memory page. This is either 4K or 8K, depending on a platform. |
| `gzip_http_version` | Sets the minimum HTTP version of a request required to compress a response. |
| `gzip_min_length`   | Sets the minimum length of a response that will be gzipped. The length is determined only from the “Content-Length” response header field. |
| `gzip_types`        | Enables gzipping of responses for the specified MIME types in addition to “`text/html`”. The special value “`*`” matches any MIME type (0.8.29). Responses with the “`text/html`” type are always compressed. |
