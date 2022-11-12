---
title: "Getting Podman and Nginx TCPv6 and HTTP/2 Ready"
date: 2022-09-28T22:43:28-04:00
draft: false
tags: ["Networking", "Containers"]
math: false
---

When checking the status of my website, I discovered that my website wasn't accessible over IPV6 and didn't have HTTP/2 enabled! This post will go over how I remedied that with my current setup of Nginx running within a podman container. Do note, TCPv6 will only work if you are provided a IPv6 address from your server provider.

## Local Verification

**For IPv6:**

A website that I used for checking if my site was accessible over IPv6 is https://ready.chair6.net/

Though there are also an array of linux tools you can use.

1. Check if the DNS records contain a `AAAA` record

Let's look at my website as an example:

```bash
dig brandonrozek.com AAAA
```

Output:

```
; <<>> DiG 9.18.1-1ubuntu1.2-Ubuntu <<>> brandonrozek.com AAAA
;; global options: +cmd
;; Got answer:
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 24248
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 1

;; OPT PSEUDOSECTION:
; EDNS: version: 0, flags:; udp: 65494
;; QUESTION SECTION:
;brandonrozek.com.              IN      AAAA

;; ANSWER SECTION:
brandonrozek.com.       2       IN      AAAA    2600:3c03::f03c:93ff:fe89:8753

;; Query time: 0 msec
;; SERVER: 127.0.0.53#53(127.0.0.53) (UDP)
;; WHEN: Wed Sep 28 22:46:22 EDT 2022
;; MSG SIZE  rcvd: 73

```

Within the answer section you can see the IPv6 address set.

Next you can check if curl can grab the webpage via IPv6. Though importantly, you must be on an Internet connection with IPv6 support to test this. One webpage you can use to test is: https://test-ipv6.com/

An example of using `curl`:

```bash
curl \
    -k \
	--header 'Host: brandonrozek.com' \
    -6 \
    https://[2600:3c03::f03c:93ff:fe89:8753]/
```

Since we're not accessing the website via the DNS record and instead the IPV6 address, the host name won't match the SSL certificate. Hence we need to add `-k` for testing so that it can accept the "insecure" certificate. For a similar reason we need to specify the host header. My webserver runs multiple websites, so not specifying that will provide the default. The flag `-6` tells curl to use IPv6. Finally the URL goes at the end with the IPv6 address wrapped in square brackets.

**For HTTP/2**

KeyCDN provides a web [tool](https://tools.keycdn.com/http2-test) to check, though luckily checking with curl on Linux is short.

```bash
curl -I https://brandonrozek.com
```

The `-I` flag means only grab the headers.

This results in:

```
HTTP/2 200 
server: nginx
date: Thu, 29 Sep 2022 03:01:50 GMT
content-type: text/html
content-length: 7946
last-modified: Wed, 28 Sep 2022 23:00:01 GMT
vary: Accept-Encoding
etag: "6334d1f1-1f0a"
accept-ranges: bytes
```

The first line will contain the string `HTTP/2` if your website supports it.

## Changes

Initially I did not have this setup, there were three edits that I needed to make on the webserver:

1. Edits to the podman network
2. Edits to the docker-compose file
3. Edits to the Nginx configuratoin

Starting from the podman network. First lets check if IPv6 is enabled:

```bash
sudo podman network inspect network_name | grep ipv6
```

If its enabled, then it will print out true as its value. If not, then we'll need to recreate the network. First you'll have to stop and remove all containers using that network. Then remove the network.

Here's an example to create a new network:

```bash
sudo podman network create \
	--ipv6 --subnet 2022:db8:abc1::/64 \
	--subnet 10.11.12.0/24 \
	network_name
```

In the docker-compose you likely have a section where you bind ports 80 and 443 in the Nginx container to the host:

```yaml
ports:
 - 80:80
 - 443:443
```

Now we need to add the TCPv6 bindings:

```yaml
ports:
 - 80:80
 - 443:443
 - :::80:80
 - :::443:443
```

Then restart the nginx container.

To see if the ports  are open on the host (ex: 443), we can use `netstat`:

```bash
sudo netstat -anlp | grep 443
```

This should return:

```
tcp   0  0  0.0.0.0:443  0.0.0.0:*  LISTEN  51911/conmon        
tcp6  0  0  :::443       :::*       LISTEN  51911/conmon
```

Where `conmon` is the connection monitor which passes traffic to the podman container.

Finally changes need to be made within the nginx configuration to use TCPv6 and HTTP/2.

Within the server directives:

```nginx
server {
    listen 80;
    listen [::]:80;
	# ....
}
server {
    listen 443 ssl http2;
    listen [::]:443 ssl http2;
    # ...
}
```

Then restart the `nginx` container and check `netstat` within the contaner.

```bash
sudo docker-compose exec nginx_container_name sh -c "netstat -anlp | grep 443"
```

This should output something similar to:

```
tcp  0  0  0.0.0.0:443  0.0.0.0:*  LISTEN  172/nginx
tcp  0  0  :::443       :::*       LISTEN  172/nginx
```

There you have it! Now your website should be TCPv6 and HTTP/2 compatible. Feel free to get in touch if you have any questions.
