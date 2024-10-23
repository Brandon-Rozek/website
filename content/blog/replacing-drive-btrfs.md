---
title: "Replacing a drive in Btrfs"
date: 2024-10-23T10:37:54-04:00
draft: false 
tags: []
math: false
medium_enabled: false
---

The following are the steps that I take to replace a hard drive in Btrfs with a drive of equal capacity or larger. These instructions are mostly taken from [Forza's Wiki](https://wiki.tnonline.net/w/Btrfs/Replacing_a_disk) which goes into much more depth.

**Step 1**: Setup a USB with a live image

It turns out that with a hard drive missing, my system would refuse to boot. To get around this, we'll need to use a live image to get to a terminal which will allow us to run the commands we need.

I did this by grabbing the latest version of [Fedora Server](https://fedoraproject.org/server/download/).

**Step 2** Get to a terminal

If we used the Fedora server image, we'll need to select "Rescue Fedora system". If it fails to boot normally, then it'll also fail at this step but will give us access to a terminal which is what we want.

**Step 3**: Mount the Btrfs file system as degraded

The Btrfs tooling expects that the filesystem is mounted. Assuming that `/dev/sda1` is one of the partitions already in the Btrfs pool, we can do the following:

```bash
mkdir /mnt/btrfs
mount -o degraded /dev/sda1 /mnt/btrfs
```

**Step 4**: Prepare the new disk (Optional)

Let's assume that `/dev/sdX` is our new disk. We can set up a `gpt` partition table using `parted`.

Open up the parted tool: `parted /dev/sdX`

```
mklabel gpt
mkpart primary btrfs 4MiB 100%
quit
```

**Step 5:** Identify missing device ID

Since we're replacing a hard drive, this means that one of the device ids is missing in the pool. We can use the following command to see which one

```bash
btrfs filesystem show
```

**Step 6:** Start the replacement process

Let's say that the missing device id is `Y`. We can then replace that device with our new drive with the following command:

```bash
btrfs replace start Y /dev/sdX /mnt/btrfs
```

This will take some time. We can check the status with:

```bash
btrfs replace status /mnt/btrfs
```

**Step 7**: Resize the filesystem (Optional)

If we replaced the disk with a larger one, we'll need to tell Btrfs the new size to take advantage of it.

```bash
btrfs filesystem resize Y:max /mnt/btrfs
```

Don't forget to replace `Y` with your device id. Also, *max* is a special keyword that btrfs recognizes so we don't need to replace it.

**Step 8**: Rebalance the filesystem

In order to ensure that our data is evenly distributed across the available hard drives, we'll need to re balance the btrfs array. Warning, this will take a very long time. I think of this as an overnight task.

```bash
btrfs balance start /mnt/btrfs
```

That's it! Restart the computer and make sure that it boots properly. Then, enjoy.
