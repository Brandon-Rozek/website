---
title: "Xvfb"
date: 2020-09-07T20:49:54-04:00
draft: false
tags: ["X11"]
medium_enabled: true
---

X Virtual Framebuffer (Xvfb) is a great quick application to run applications that expect a `X11` server, but you don't care to see the visual output.

To install:

```bash
sudo apt install xvfb
```

To run:

```bash
xvfb-run application
```

For more customization, I hear that it's better to use [xpra with Xdummy](https://web.archive.org/web/20200926082251/https://xpra.org/trac/wiki/Xdummy). I haven't tried this myself yet, but if you experience issues with the application expecting `randr` or `glx` extensions, give it a shot.