---
title: "Chroot and Virtual Filesystems"
date: 2020-11-29T10:52:07-05:00
draft: false
tags: []
---

When running applications under a [`chroot`](https://en.wikipedia.org/wiki/Chroot) environment, it can be annoying when certain [virtual filesystems](https://opensource.com/article/19/3/virtual-filesystems-linux) are unavailable. Here are the commands to mount the most common ones:

```bash
sudo mount -t proc /proc /mnt/root/proc
sudo mount -o bind /sys /mnt/root/sys
sudo mount -o bind /dev /mnt/root/dev
```

Source: [ArchWiki](https://wiki.archlinux.org/index.php/chroot)

