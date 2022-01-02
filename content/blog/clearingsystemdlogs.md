---
title: "Clearing Systemd Logs"
date: 2021-02-21T16:08:51-05:00
draft: false
tags: ["Linux"]
---

Short post today. I wanted to clear out some disk space usage on one of my servers and noticed that the systemd logs were taking up a decent bit. Here are two options to clear out old logs.

Here is an example to do it by time, let's say 15 days:

```bash
journalctl --vacuum-time=15d
```

An example to clear it by total disk usage, let's say 10Gb:

```bash
journalctl --vacuum-size=10G
```

