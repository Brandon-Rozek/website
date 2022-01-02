---
title: "Scrcpy"
date: 2020-01-09T21:36:30-05:00
draft: false
tags: [ ]
---

With [Scrcpy](https://github.com/Genymobile/scrcpy) you can control an Android device remotely!

![1578623897330](/files/images/1578623897330.png)

The `README` on the Github page has all the information you need though it boils down to a few simple steps.

1. Install `scrcpy`. 
```bash
sudo snap install scrcpy
```
2. [Enable adb debugging](https://developer.android.com/studio/command-line/adb.html#Enabling) on your device
3. (Optional for remote capability) Enable adb over TCP/IP on your device
```bash
adb tcpip 5555
```
4. (Optional Continued) Connect to the device
 ```bash
 adb connect DEVICE_IP:5555
 ```
 5. Run `scrcpy`
