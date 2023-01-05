---
title: "Virtual Disks"
date: 2020-01-06T22:26:58-05:00
draft: false
tags: [ "Linux", "Storage" ]
medium_enabled: true
---

Have you wanted to [play with ZFS](https://wiki.archlinux.org/index.php/ZFS/Virtual_disks) or any other filesystem without creating a dedicated partition or device? We can do this through virtual disks!

First, we need to create a [sparse file](https://en.wikipedia.org/wiki/Sparse_file) called `scratch.img` with some max capacity. Let's say 2G.

```bash
truncate -s 2G $HOME/scratch.img
```

Now the file is only sparse, if your filesystem supports it. To see, run `du -sh $HOME/scratch.img`. If it says that the size is `0` then your filesystem supports sparse files. Otherwise it does not.

Then, we can format the file with any filesystem we will like. One popular tool is `mkfs` which depending on your operating system can support [`bfs`](https://en.wikipedia.org/wiki/Be_File_System), [`cramfs`](https://en.wikipedia.org/wiki/Cramfs), [`ext2`](https://en.wikipedia.org/wiki/Ext2), [`ext3`](https://en.wikipedia.org/wiki/Ext3), [`ext4`](https://en.wikipedia.org/wiki/Ext4), [`fat`](https://en.wikipedia.org/wiki/File_Allocation_Table), [`minix`](https://en.wikipedia.org/wiki/MINIX_file_system), `msdos`, [`ntfs`](https://en.wikipedia.org/wiki/NTFS), [`vfat`](https://en.wikipedia.org/wiki/File_Allocation_Table#VFAT), [`reiserfs`](https://en.wikipedia.org/wiki/ReiserFS), etc.

To format with `ext4`,

```bash
mkfs -t ext4 $HOME/scratch.img
```

Then we can create the mount-point `/mnt/scratch` and mount `scratch.img` to it.

```bash
sudo mkdir /mnt/scratch
sudo mount -t auto -o loop $HOME/scratch.img /mnt/scratch
```

With this, we now have a mounted `ext4` filesystem on `/mnt/scratch`. `cd` into it and have a blast!

## Resizing the Virtual Disk

To resize the virtual disk, we will first need to unmount the virtual disk so we don't create inconsistencies.

```bash
sudo umount /mnt/scratch
```

Now we can extend or shrink the drive with `truncate`.

Extend by 1G: `truncate -s +1G $HOME/scratch.img`

Shrink by 1G: `truncate -s -1G $HOME/scratch.img`

Check the filesystem to make sure that no inconsistencies occurred. With `ext(2/3/4)` we can do this with the `e2fsck` command.

```bash
e2fsck $HOME/scratch.img
```

Then we need to tell the filesystem to resize itself. For `ext(2/3/4)` you can do this with the `resize2fs` command.

```bash
resize2fs $HOME/scratch.img
```

Now the virtual disk is successfully resized! We can mount it back with the previous mount command.

```bash
sudo mount -t auto -o loop $HOME/scratch.img /mnt/scratch
```

## Removing the Virtual Disk

To remove the virtual disk, we first need to unmount the virtual drive

```bash
sudo umount /mnt/scratch
```

Then we can remove the mount-point and file.

```bash
sudo rm -r /mnt/scratch
rm $HOME/scratch.img
```

## Conclusion

With virtual disks we can experiment with different types of filesystems and perhaps try out snapshoting in supported filesystems. If we create virtual disks on [`tmpfs` ](/blog/lxdtmpfs/), then we can have a super fast file system as well!
