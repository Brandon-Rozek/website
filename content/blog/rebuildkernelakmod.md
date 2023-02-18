---
date: 2022-02-04 19:37:04-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: ab0e2a2ce3b3
tags:
- Linux
- Fedora
title: Rebuild Kernel Modules with Akmods
---

Akmods is the Fedora/Red Hat way of managing kernel modules. In Ubuntu, this is `dkms`. If you're like me and force reboot shortly after performing an update, then you might have not given akmods enough time to compile any extra kernel modules (for example: Nvidia). This meant that I had to boot into an older kernel to try to fix the problem....

Once in the older kernel, you can check the kernel versions by:

```bash
ls /usr/src/kernels/
```

Then select the kernel which you failed to build and run:

```bash
sudo akmods --kernels 5.15.18-200.fc35.x86_64
```

to trigger the rebuild.

Though the better solution is to avoid this problem to begin with.
If you `reboot` not as root, then systemd will check to see if
any process is inhibiting the poweroff. If that's the case,
wait patiently and don't type `sudo reboot`.