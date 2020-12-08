---
title: "Burning ISOs with dd/pv"
date: 2020-01-20T10:23:20-05:00
draft: false
tags: [ "linux" ]
---

While there are nice graphical tools like [Etcher](https://www.balena.io/etcher/), what is almost always a constant is the tool `dd`. Therefore, for future reference I'll just paste the `dd` command I use to make ISO images.

```bash
sudo dd bs=4M if=image.iso of=/dev/sdX status=progress oflag=sync
```

Alternatively you can use `pv`

```bash
pv image.iso > /dev/sdX
```

