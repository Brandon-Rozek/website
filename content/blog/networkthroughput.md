---
title: "Network Throughput Testing"
date: 2019-08-30T20:11:26-04:00
draft: false
tags: [ "linux", "network" ]
---

I ended up upgrading the wiring in my place to CAT7 recently and I wanted to see if there was a noticeable performance difference to my previous cabling. This blog post won't be a product comparison, but instead I'll show how you can do network throughput testing at your own location.

There is a great package called `iperf3`. It's in most repositories under Linux, and binaries for Windows and macOS exist as well.

For a more in depth tutorial [check out this post from Linode](https://www.linode.com/docs/networking/diagnostics/install-iperf-to-diagnose-network-speed-in-linux/).

*For the 5 second spiel...*

One one machine, start the server

```bash
iperf3 -s
```

On another machine connect to the server and begin testing the connection

```bash
iperf3 -c 192.168.0.2
```

You can also use the `-t` flag to specify the number of seconds you want to run the test for.
