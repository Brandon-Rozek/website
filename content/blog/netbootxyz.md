---
date: 2021-06-18 19:43:29
draft: false
medium_enabled: true
medium_post_id: d99cafd95a34
tags: []
title: Netboot.xyz Bootloader
---

Instead of manually loading ISOs onto a USB stick for [Ventoy](/blog/ventoy/) to display, we can use Netboot.xyz to present us a list of options and download them during boot. This requires an internet connection in order to work.

Netboot.xyz is commonly used for PXE booting, but in this post I'll describe using it as an ISO.

Download the [Netboot ISO](https://boot.netboot.xyz/ipxe/netboot.xyz.iso) and [load it onto a flash drive](/blog/ddforiso/). Then boot a computer from the flash drive and you should see something similar to this animation from their website:

![](/files/images/blog/netboot.xyz.gif)

Another benefit of this approach over Ventoy is that we don't have to manually update the flash drive. It always comes fresh with the ISOs available on their website.