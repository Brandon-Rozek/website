---
title: "Analyzing Startup Times with Systemd"
date: 2019-12-26T22:52:59-05:00
draft: false
tags: [ "Linux" ]
medium_enabled: true
---

Startup times feeling slow? Check to see if there are any uneeded services slowing you down!

To see how long it takes to bootup

```bash
systemd-analyze
```

To see the length of time each service took to initialize

```bash
systemd-analyze blame
```

Then you can `disable` any services that you don't need.

