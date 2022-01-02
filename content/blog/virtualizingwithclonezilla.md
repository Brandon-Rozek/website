---
title: "Virtualizing Environments with Clonezilla"
date: 2019-08-25T20:09:28-04:00
draft: false
tags: ["Virtualization"]
---

[Clonezilla](https://clonezilla.org/) advertises itself as a disk cloning and backup utility. I've been starting to think of it as a little more than that. Let's say that you go to a client site and they have a machine in production. Instead of messing around with their machine, you make a Clonezilla copy of it.  You can then take it back and place it on a computer you're not using to play around with it.

Now even better, instead of using bare metal, what if you virtualize it? It's essentially the same process as putting it on baremetal, except now you have a virtual copy that you can make clones of, backup, etc.

Now if the OS is looking for hardware that doesn't exist, that might make life a bit harder....