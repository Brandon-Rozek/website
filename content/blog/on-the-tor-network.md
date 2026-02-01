---
title: "Bringing this website to the Tor network"
date: 2026-02-01T17:47:15-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

I believe in the freedom of information. By making my website available as a Tor hidden service, you can be sure to access the information even if it's blocked on the clearweb.

In this post, I'll share the steps I took and what I learned along the way. Huge credit to Christian [who wrote their own succinct version](https://cleberg.net/blog/self-hosting-tor.html) of this post and helped me troubleshoot via email.

### Getting an Address

Unlike the clear web, we don't register a domain with anyone. [An address on Tor is a hash of your public key.](https://github.com/torproject/torspec/blob/main/rend-spec-v3.txt)

This is why onion URLs are long and unreadable. Take a look at the following onion URL which takes you to the Tor homepage.
```
http://2gzyxa5ihm7nsggfxnu52rck2vv4rvmdlkiu3zzui5du4xyclen53wid.onion
```

Notice that the address starts with `http`. Unlike the clearweb, *all* traffic via Tor is encrypted. Our hidden service will use the public key behind the URL during the protocol exchange.

The primary benefit of these addresses are that they are entirely decentralized (we create our own keys). They are also incredibly difficult to spoof. The downside is that they are not human readable. We can get a little bit closer to that though with vanity keys.

To create a vanity key, we can use [mkp224o](https://github.com/cathugger/mkp224o#requirements). After following the installation instructions, we can create our own onion URL starting with some `prefix` by running the following:

```
./mkp224o prefix
```

Given the current algorithms and hardware, we can easily generate keys which have a URL prefix length of up to six characters in minutes. Beyond that, the generation quickly becomes infeasible... However, we want this to be the case. If it was feasible to generate a key-pair for an entire onion URL then anyone can spoof your hidden service.

The script by default will create many folders in the current directory which have the onion URLs as their name and the contents of the keys within. Pick your favorite and copy it over to `/var/lib/tor/somehiddenservicename`.

**While you're at it, make a backup of these keys because if we lose it then we lose control over the domain.** 


## Installing and Configuring Tor

Now that we have our address. Let's get Tor installed and set up. In this guide, I'll show how to do so via Podman Quadlets.

We'll use the Docker container [dockur/tor](https://github.com/dockur/tor). Since Tor is a cryptographic software, we need to be extremely careful where we download it from. As of this time of writing if we look at the Dockerfile in this repo, we can see that this is a simple wrapper over Alpine's tor packages. Currently, I feel that it's safe to trust the Alpine maintainers.

After selecting the Docker container, we need to write the Quadlet definition file. Here's how I have `/etc/containers/systemd/tor.container` configured:

```ini
[Container]
ContainerName=tor
HostName=tor
Image=docker.io/dockurr/tor
AutoUpdate=registry
Volume=/etc/tor:/etc/tor:ro,Z
Volume=/var/lib/tor:/var/lib/tor:Z,U

[Service]
Restart=always

[Install]
WantedBy=default.target
```

Before we run it, we'll need to create our main Tor configuration file. This lives in `/etc/tor/torrc`.

```
SocksPort 0
HiddenServiceDir /var/lib/tor/somehiddenservicename
HiddenServicePort 80 IP_OF_NGINX_CONTAINER:80
```

Replace `IP_OF_NGINX_CONTAINER` with the internal IP of the Nginx container or of the host machine if it is running on there. Here's an explanation of each line:

| Key                 | Value                                                        |
| ------------------- | ------------------------------------------------------------ |
| `SocksPort`         | By default, the tor service will open a SOCKS port so that we can have other HTTP clients proxy to the dark web. Setting this to 0 disables that behavior. |
| `HiddenServiceDir`  | The location of our hostname file and the keys for our hidden service. |
| `HiddenServicePort` | The port on the Tor network followed by the `address:port` to proxy the traffic to. We may have multiple of these per hidden service. |

Since we're proxying traffic to our application, let's configure our target next.

## Configuring Nginx

My website is a static site served by Nginx. These files are linked together via absolute URLs. This adds some complications because the onion hidden service URL is completely different than my clearnet one.

One solution would be to make my URLs relative. However, I want my website to be as portable as possible. For example, you can run my website in a subfolder. Thus, our solution here is to have an entirely separate copy of the website where the only difference is the internal URLs.

I've set this version of my website to live in `/var/www/brozekhs`.

As such, we have to create an Nginx configuration file solely for our hidden service. We'll make sure to point the root to the folder which contains the hidden service version of my website.

```nginx
server {
    listen 80;
    server_name ONION_URL;

	root /var/www/brozekhs;
    index index.html;

	# ...

	location / {
		allow IP_OF_TOR_CONTAINER;
        deny all;
        # ...
	}
}
```

Replace `/var/www/brozekhs`, `ONION_URL` and `IP_OF_TOR_CONTAINER` with their respective values. We need to configure the `allow` and `deny` lines because we don't want someone to confirm that our machine responds to tor addresses over the clearnet.

After this when running my `nginx` container I came across the following error:
```
date time [emerg] 1#1: could not build server_names_hash, you should increase server_names_hash_bucket_size: 64
```

As stated, the solution is to increase the server name hash bucket size. I doubled it from 64 to 128 in the `http` block of `/etc/nginx/nginx.conf`:

```
server_names_hash_bucket_size 128;
```

Lastly if you have a clearnet site and you want to advertise the onion URL for users visiting the clearnet URL on the Tor browser, then we can add an [`Onion-Location` header](https://community.torproject.org/onion-services/advanced/onion-location/) to the Nginx config of our clearnet site.


```nginx
location / {
	# ...
    add_header Onion-Location ONION_URL$request_uri;
}
```

Replace `ONION_URL` with your own and make sure that `$request_uri` stays at the end of the header value. This will help the Tor browser with the redirection.

## Start em up!

With that, we can start our two services:
```
sudo systemctl start nginx
sudo systemctl start tor
```

When we look at `journalctl -U tor`, we should see something like the following:
```
datetime hostname systemd[1]: Started tor.service.
datetime hostname tor[681220]: datetime [notice] Tor can't help you if you use it wrong! Learn how to be safe at https://support.torproject.org/faq/staying-anonymous/
datetime hostname tor[681220]: datetime [notice] Read configuration file "/etc/tor/torrc".
datetime hostname tor[681220]: datetime [notice] Parsing GEOIP IPv4 file /usr/share/tor/geoip.
datetime hostname tor[681220]: datetime [notice] Parsing GEOIP IPv6 file /usr/share/tor/geoip6.
datetime hostname tor[681220]: datetime [notice] Bootstrapped 0% (starting): Starting
datetime hostname tor[681220]: datetime [notice] Starting with guard context "default"
datetime hostname tor[681220]: datetime [notice] Bootstrapped 5% (conn): Connecting to a relay
datetime hostname tor[681220]: datetime [notice] Bootstrapped 10% (conn_done): Connected to a relay
datetime hostname tor[681220]: datetime [notice] Bootstrapped 14% (handshake): Handshaking with a relay
datetime hostname tor[681220]: datetime [notice] Bootstrapped 15% (handshake_done): Handshake with a relay done
datetime hostname tor[681220]: datetime [notice] Bootstrapped 45% (requesting_descriptors): Asking for relay descriptors
datetime hostname tor[681220]: datetime [notice] Bootstrapped 50% (loading_descriptors): Loading relay descriptors
datetime hostname tor[681220]: datetime [notice] Bootstrapped 55% (loading_descriptors): Loading relay descriptors
datetime hostname tor[681220]: datetime [notice] Bootstrapped 60% (loading_descriptors): Loading relay descriptors
datetime hostname tor[681220]: datetime [notice] Bootstrapped 66% (loading_descriptors): Loading relay descriptors
datetime hostname tor[681220]: datetime [notice] Bootstrapped 75% (enough_dirinfo): Loaded enough directory info to build circuits
datetime hostname tor[681220]: datetime [notice] Bootstrapped 90% (ap_handshake_done): Handshake finished with a relay to build circuits
datetime hostname tor[681220]: datetime [notice] Bootstrapped 95% (circuit_create): Establishing a Tor circuit
datetime hostname tor[681220]: datetime [notice] Bootstrapped 100% (done): Done

```

We won't be able to access the hidden service until the bootstrapping process reaches 100%. Depending on the state of the network, this might take awhile...

I mention the network state since it's common for me to see this in the logs:
```
datetime hostname tor[295456]: datetime [warn] Detected possible compression bomb with input size = 17413 and output size = 515472 (compression factor = 29.60)
datetime hostname tor[295456]: datetime [warn] Possible compression bomb; abandoning stream.
datetime hostname tor[295456]: datetime [warn] Detected possible compression bomb with input size = 23289 and output size = 774624 (compression factor = 33.26)
datetime hostname tor[295456]: datetime [warn] Possible compression bomb; abandoning stream.
```

This compression or [zip bomb](https://en.wikipedia.org/wiki/Zip_bomb) appears to be an attempt at a distributed [denial of service attack](https://en.wikipedia.org/wiki/Denial-of-service_attack). Luckily, the Tor software is smart enough to guard against this.

Every so often my Tor service goes down and I need to restart the daemon for it to come back up. I haven't gotten around to writing monitoring scripts for my hidden service so if anyone has any tips feel free to get in touch.
