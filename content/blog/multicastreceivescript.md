---
title: "Multicast Receive Script"
date: 2020-11-18T10:09:15-05:00
draft: false
tags: []
---

I use `socat` to debug mutlicast traffic, though the syntax for it is complicated to learn. Here is the command that I normally use to debug multicast traffic.

```bash
socat UDP4-RECVFROM:"$port",ip-add-membership="$multicast_address":0.0.0.0,fork -
```

This says to:

- Listen to UDP traffic from `$port`.
- Subscribe to `$multicast_address`.
- `0.0.0.0` means to do it from the interface that matches the routing table for the multicast address.
- The rest makes it print the traffic to standard out.

To make life easier I created a little script called `mrecv` that takes a multicast address and port and forms the socat command for me.

```bash
#!/bin/bash

show_usage() {
    echo "Usage: mrecv [multicast_address] [port]"
    exit 1
}

contains_help_flag() {
    if [ "$1" = "-h" ] || [ "$1" = "--help" ]; then
        return 0
    fi
    return 1
}

if [ "$#" -ne 2 ] ||
   contains_help_flag "$1" ||
   contains_help_flag "$2"; then
    show_usage
fi

multicast_address="$1"
port="$2"

socat UDP4-RECVFROM:"$port",ip-add-membership="$multicast_address":0.0.0.0,fork -
```

