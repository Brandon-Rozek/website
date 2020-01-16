---
title: "External Media Formats"
date: 2019-05-22T22:03:38-04:00
draft: false
---

I received an external SSD recently and I decided that it would be a great place to offload some of my backups. Before I got started, I became curious as to what filesystem to put on the SSD. After some research, it seems that if I want to be able to access it using Windows I am actually quite limited. In fact only three make sense:

- FAT32
- exFAT
- NTFS

Now FAT32 is a legacy filesystem, Windows 95 type of legacy. So let's rule that one out. exFAT is supposed to be based on FAT32 but increases the file size limits significantly. It is also known for being very slim and as such does not having journaling support. NTFS is the filesystem that Windows 10 uses for default for it's installation. That file system supports journaling.

I ended up going with NTFS due to its journaling support. Why is journaling important to me? Well this helps keep the file system internally consistent. The details are outside the scope of this post, but [Wikipedia has a nice entry](https://en.wikipedia.org/wiki/Journaling_file_system) about it.

Well as it turns out, the drive that I was going to use already was formatted as NTFS. Though for sake of completeness, I will say that you can format drives with tools like `parted`, `gparted`, and `partitionmanager`. Just make sure that the drive you're formatting is what you think it is!

