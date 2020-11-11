---
title: "Custom Device Paths with UDEV rules"
date: 2020-11-10T20:58:37-05:00
draft: false
tags: []
---

I wanted to create a rule so that when I plug in my rtlsdr, a symlink to the device will appear in `/dev/rtlsdr`.

To do this, first we need to get some uniquely identifying information about the SDR.

```bash
❯ lsusb
Bus 001 Device 002: ID 8087:8001 Intel Corp. Integrated Hub
Bus 001 Device 001: ID 1d6b:0002 Linux Foundation 2.0 root hub
Bus 003 Device 001: ID 1d6b:0003 Linux Foundation 3.0 root hub
Bus 002 Device 017: ID 0bda:2838 Realtek Semiconductor Corp. RTL2838 DVB-T
Bus 002 Device 001: ID 1d6b:0002 Linux Foundation 2.0 root hub
```

The part we care about here is the ID field. It is structured as `ID vendor:product`.

Now we can create a UDEV rule in `/etc/udev/rules.d/` that says "when we see this specific USB plugged in, create a symlink called `rtlsdr`"

(/etc/udev/rules.d/rtlsdr.rules)

```
SUBSYSTEM=="usb", ATTR{idVendor}=="0bda", ATTR{idProduct}=="2838", SYMLINK+="rtlsdr"
```

Once you have your device plugged in, you should be able to see it under `/dev/rtlsdr` or whatever you specified your symlink as.