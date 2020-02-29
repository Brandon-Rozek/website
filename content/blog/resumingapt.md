---
title: "Resuming Stopped Apt Updates"
date: 2020-02-29T17:58:14-05:00
draft: false
tags: ["ubuntu", "linux"]
---

Especially on the Raspberry Pi, it is quite often for me to lose connection while updating. I know some people setup `screen` or `tmux` sessions so that they can easily reconnect. I'm not good at remembering to do this. [Angus and Cas](https://unix.stackexchange.com/a/46546) on StackExchange shared that to resume a stopped update...

```bash
sudo kill $(pgrep dpkg)
sudo dpkg --configure --pending
sudo apt install -f
```

Which will then configure the packages that have already been installed but not configured yet and finish installing packages.