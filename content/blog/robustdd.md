---
title: "Robustdd"
date: 2019-09-27T22:45:56-04:00
draft: false
tags: [ "Linux" ]
medium_enabled: true
---

This blog post is going to assume that we're writing to `/dev/sdX`. Please change this to whatever disk you're actually trying to write to. I bear no responsibility if you accidentally write to your OS drives.

Make sure the disk you wish to write to is unmounted. 

```bash
sudo umount /dev/sdX
```

For good measure check `lsblk`....

Then perform the writing operation

```bash
sudo dd bs=4M if=/path/to/distro.iso of=/dev/sdX conv=fdatasync status=progress
```

`fdatasync` will wait until the data is physically written into the drive before finishing.

Once that operation is done we can check to see if it is performed properly. This step will only work for ISOs that have prepared a file similar to `md5sum.txt` that Ubuntu provides....

```bash
sudo mount /dev/sdX /mnt
cd /mnt
md5sum -c md5sum.txt
```

Hopefully you'll see all `OK` and we're good to go!
