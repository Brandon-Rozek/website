---
title: "Wacom and USB Redirection in Virtual Machines"
date: 2019-05-24T22:15:56-04:00
draft: false
tags: [ "linux" ]
---

[Virt-Manager](https://virt-manager.org/) is a great tool for managing virtual machines under Linux. Today I learned of [Spice USB redirection](https://blog.wikichoon.com/2014/04/spice-usb-redirection-in-virt-manager.html). Essentially it allows you to switch USB devices from the host to the virtualized environment. This came in handy when I noticed that the graphics tablet device was not able to do pressure sensitivity on the Windows guest. 

To achieve this goal, I removed the graphics tablet hardware device and manually redirected that USB device to the guest. I then remembered to install the [Wacom drivers](https://www.wacom.com/en-us/support/product-support/drivers) for the Windows VM.
