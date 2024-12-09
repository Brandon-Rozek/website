---
title: "Temporary Port Forward using UPnP in Linux"
date: 2024-12-08T21:04:51-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

I don't know about you, but I don't particularly enjoy logging onto my router. *Especially since the web UI differs between router models.* Unfortunately, a common step of hosting a multiplayer game server at home is to set up a port forward.

This tells your router to take traffic coming in at a specified external *port*, and *forward* it to one of your computer's internal IP address at a specified local port.

![Port Forward Diagram](/files/images/blog/PortForward.svg)

What if I tell you that instead of having to login to your router interface every time you want to set up a port forward, you can programatically perform it from your Linux machine? This is where Universal Plug and Play (UPnP) comes in. Some games even automatically manage this for you!

Since router configurations vary widely, we'll assume that you already have UPnP enabled. Not all routers, however, support this. Look up the model of your router with UPnP to see if yours does. For example, [here's how to set it up within pfSense](https://docs.netgate.com/pfsense/en/latest/services/upnp.html). 

Enabling UPnP by default means allowing any computer in your network to modify port forwarding. For security reasons, you'll likely want to restrict this to a few trusted machines, i.e. game consoles and laptops.

In order to manage UPnP from a Linux machine, we'll need the `upnpc` command. This can be found in the `miniupnpc` package on Fedora.

```bash
sudo dnf install miniupnpc
```

From here, we can check if we've enabled UPnP by querying for its status

```bash
upnpc -s
```

If it returns the following, then UPnP is not properly set up!

```
No IGD UPnP Device found on the network !
```

Otherwise you'll get a lot of information including:

```
Found valid IGD : <REDACTED URL>
```

Assuming everything is setup correctly, we'll run through an example. Say that we want to run a Starbound server. This typically runs on port `21025`.

```bash
export INTERNAL_PORT=21025
```

We'll need to know our computer's internal IP address. Assuming that `1.0.0.0` will take you to the Internet and not some virtual private network, we can run the following to get our internal IP address

```bash
export INTERNAL_IP=$(ip route get 1 | awk '{print $7}')
```

For the external port that our friends will connect to, we'll need to pick an arbitrarily high number that's not already assigned. This number can be between 1024-65535 depending on your UPnP configuration.

For example,

```bash
export EXTERNAL_PORT=60821
```

Lastly, we need to know whether our game server accepts TCP or UDP requests.  Starbounds expects TCP requests.

```bash
export PROTOCOL=TCP
```

Now we can issue a command to our router using `upnpc` to forward traffic on the external port to our local computer at the specified internal port.

```bash
upnpc -a $INTERNAL_IP $INTERNAL_PORT $EXTERNAL_PORT $PROTOCOL
```

From here, people outside of your network should be able to send traffic to your local computer! They'll need to know your external IP address.

```bash
upnpc -s | grep Ext
```

If your friends are having trouble connecting to your external IP address and port, double check that your local computer's firewall isn't blocking the traffic and check the UPnP routing list.

```bash
upnpc -l
```

When you're done, don't forget to delete the rule from UPnP.

```bash
upnpc -d $EXTERNAL_PORT $PROTOCOL
```

Other than gaming, another use case for this is file transfer.  Say you want to receive a file from a friend. To not repeat details, assume we're using the same variables from above and you already added the port forward to UPnP.

On your local machine, use `netcat` to listen for traffic and write the bytes received to a file.

```bash
nc -l $INTERNAL_PORT > file_received.txt
```

Your friend can now send you a file.

```bash
nc $EXTERNAL_IP $EXTERNAL_PORT < file_to_send.txt
```

