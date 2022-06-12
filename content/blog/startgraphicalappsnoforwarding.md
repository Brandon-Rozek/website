---
title: "Starting Graphical Applications Remotely without X-Forwarding"
date: 2020-09-07T20:24:49-04:00
draft: false
tags: []
---

One of my favorite casual gaming setups is to use a slim laptop on my couch while streaming from my desktop using Steam Remote Play.  The downside though is that unless I want to get up, Steam needs to be already running on my desktop. This post describes how I start steam remotely from my couch so that I can stream my games without having to get up and set it up on my desktop first.

This requires you to be already logged into a graphical session on the computer you want to stream from. 

On Linux, there is a DISPLAY environmental variable which tells X11 where to show the application. By default (at least on Ubuntu), the display starts as `:0` and moves up in count. We can make use of this fact, to start steam on a X11 server instance that is already running so that we don't have to do any X11 forwarding.

On the client computer,

```bash
ssh desktop "DISPLAY=:0 nohup steam"
```

The `nohup` allows the application to not terminate when you press `CTRL-C` from your client computer.

Update: In light of [discovering `systemd-run`](/blog/launchappsthroughterminal/), I recommand you
do the following instead:

```bash
ssh desktop "DISPLAY=:0 systemd-run --user steam"
```
