---
title: "V4l2 Webcam"
date: 2020-05-25T23:49:08-04:00
draft: false
tags: ["Audio-Video"]
---

In Linux you can create a fake webcam by making use of the `v4l2loopback` kernel module.

To install,

```bash
sudo apt install v4l2loopback-dkms
```

If you already had an existing module, remove it so we can customize it.

```bash
sudo modprobe -r v4l2loopback
```

Then create the file `/etc/modprobe.d/fakecam.conf` and add the following line

```
options v4l2loopback devices=1 video_nr=20 card_label=fakecam exclusive_caps=1
```

The value of `video_nr` must be larger than the amount of cameras in your system. I wouldn't have more than 10 webcams plugged into my system, so I set it to 20.

Then load back up the kernel module

```bash
sudo modprobe v4l2loopback
```

Now when you open up Chrome, Skype, etc, you should see a new device labeled "fakecam".