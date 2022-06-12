---
title: "Playing with Live CDs"
date: 2020-01-12T22:45:06-05:00
draft: false
images: []
tags: [ "Virtualization" ]
---

I was curious on how Lubuntu 19.10 looked but I didn't feel like rebooting my computer and loading into a new ISO. Luckily there is a nice easy way to play around with live CDs.

Here's the command

```bash
virt-install --name=Lubuntu \
  --nodisks  --livecd \
  --graphics spice \
  --vcpu=4 \
  --ram=4096 \
  --os-type=linux \
  --sound \
  --accelerate \
  --cdrom=$HOME/Downloads/lubuntu-19.10-desktop-amd64.iso
```

The arguments mean the following

| Argument   | Meaning                                                      |
| ---------- | ------------------------------------------------------------ |
| nodisks    | No storage disks are created                                 |
| livecd     | Set the boot to the cdrom after installation                 |
| graphics   | Sets the graphics mode                                       |
| vcpu       | Number of virtual CPUs                                       |
| RAM        | Size of RAM                                                  |
| os-type    | Linux/Windows/etc.                                           |
| sound      | Attach a virtual audio device                                |
| accelerate | Make use of the KVM or KQEMU kernel acceleration capabilities if available. |
| cdrom      | Location of ISO                                              |

Once you run this command once, the image is "installed". This means that we can easily access it in the future with the following commands

```bash
virsh start Lubuntu
virt-viewer Lubuntu
```

![1578887790276](/files/images/blog/1578887790276.png)