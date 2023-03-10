---
date: 2020-11-29 18:45:28
draft: false
medium_enabled: true
medium_post_id: f765346971a5
tags:
- Linux
title: Autostart Desktop Applications
---

The [freedesktop specification](https://specifications.freedesktop.org/autostart-spec/0.5/ar01s02.html) describes how to identify file types, launch applications, and other useful desktop functions. A useful spec I've found recently is for launching desktop applications when you log into your machine.

In my Kubuntu 20.10 system, the directory `$HOME/.config/autostart` can contain [`.desktop`](/blog/linuxdesktopicons/) files that describes the applications to start on login. Drop whichever desktop file you wish to start there. In other systems it may be located under `$XDG_CONFIG_DIRS/autostart`.

If you want to start up a script instead, you can put the script under `$HOME/.config/autostart-scripts`.