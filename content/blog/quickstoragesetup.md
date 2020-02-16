---
title: "Quickly Setting up a Storage Device"
date: 2020-01-12T21:43:26-05:00
draft: false
tags: [ "linux", "storage" ]
---

This post exists mostly to aid myself for when I buy new drives for my home server. It's a quick and easy way to create an ext4 filesystem over the entire drive.

To go through this post, you'll need to know the name of your drive. 

```bash
sudo fdisk -l
```

or

```bash
lsblk
```

The drive is most likely one of the larger devices with no partitions set. It'll likely be of the format `/dev/sdX`.

To begin, we'll have to set the label. Here we'll use `gpt`.

```bash
sudo parted /dev/sdX mklabel gpt
```

Then we can create a primary partition formatted with ext4 covering the entire device.

```bash
sudo parted -a opt /dev/sdX mkpart primary ext4 0% 100%
```

Now we can let `ext4` format the drive,

```bash
sudo mkfs.ext4 /dev/sdX
```

I like to set up my mount points to be `/mnt/data/N` where N is the number of the drive I'm working with.

```bash
sudo mkdir /mnt/data/N
```

To temporarily mount it, just to make sure it works you can run

```bash
sudo mount /dev/sdX /mnt/data/N
```

You can unmount it with `umount`

```bash
sudo umount /dev/sdX
```

When you're ready to make it permanent, we'll have to edit the `/etc/fstab` file. We should note the drive by its UUID so that it's not dependent on the slot the hard drive sits in. You can find it by running this command 

```bash
lsblk -o UUID /dev/sdX1
```

Now you can append your `/etc/fstab` with the following:

```bash
UUID=uuid-here /mnt/data/N ext4 defaults 0 0
```

