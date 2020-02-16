---
title: "MergerFS"
date: 2020-01-14T23:10:17-05:00
draft: false
tags: [ "linux", "storage" ]
---

[MergerFS](https://github.com/trapexit/mergerfs) is a great filesystem for an expandable storage system in a homelab. Mostly since it allows you to add disks one at a time without having to, for example, resilver a ZFS pool. MergerFS won't be as efficient as a filesystem that stripes your data across disks, but in the case of a disk failure the disks unaffected will still have part of the data.

[Plenty](https://blog.linuxserver.io/2017/06/24/the-perfect-media-server-2017/) of other [people](https://www.teknophiles.com/2018/02/19/disk-pooling-in-linux-with-mergerfs/) described MergerFS, so I'll keep this post simple.

First install MergerFS,

```bash
sudo apt install mergerfs
```

The way I have my drives in my homelab setup is to have `/mnt/data/N` where `N` is the number of the drive.

Examples: `/mnt/data/1`, `/mnt/data/2`, `/mnt/data/3`

This is mainly so that I can use wildcards to capture all the drives at once.

Temporary mounting solution:

```bash
sudo mergerfs -o defaults,allow_other,use_ino,fsname=data /mnt/data/\* $HOME/data
```

Permanent solution (Edit `/etc/fstab`)

```bash
/mnt/data/* /home/user/data fuse.mergerfs defaults,allow_other,use_ino,fsname=data 0 0
```

Quick summary of options passed

| Option      | Description                                                  |
| ----------- | ------------------------------------------------------------ |
| defaults    | Shortcut for atomic_o_trunc, auto_cache, big_writes, default_permissions, splice_move, splice_read, splice_write |
| allow_other | Allows users beside the mergerfs owner to view the filesystem. |
| use_ino     | MergerFS supplies inodes instead of libfuse                  |
| fsname      | Name of the mount as shown in `df` and other tools           |

