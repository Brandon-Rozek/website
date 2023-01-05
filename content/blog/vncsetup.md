---
title: "VNC Setup"
date: 2019-05-24T23:21:43-04:00
draft: false
medium_enabled: true
---

I mostly following this [Digital Ocean Tutorial](https://www.digitalocean.com/community/tutorials/how-to-install-and-configure-vnc-on-ubuntu-18-04) on getting a working VNC setup on my desktop computer. There is one main difference on my end since I use KDE. I edited the `/home/$USER/.vnc/xstartup` file to appear as

```bash
#!/bin/sh
unset SESSION_MANAGER
unset DBUS_SESSION_BUS_ADDRESS
dbus-launch --exit-with-session startkde
```

And I added the following script to make my life easier

```bash
#!/bin/bash
ssh -L 5901:127.0.0.1:5901 -C -N -l rozek 192.168.0.104 &
krdc vnc://127.0.0.1:5901
```

