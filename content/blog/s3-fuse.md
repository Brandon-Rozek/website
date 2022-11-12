---
title: "Mount Object Storage Locally using S3 Fuse"
date: 2022-02-04T23:39:25-05:00
draft: false
tags: ["Storage"]
math: false
---

On most cloud providers, object storage is cheaper than paying for the equivalent size in block storage. Using FUSE, we can mount S3 compatible object storage with the command `s3fs`. Do note, that there are a few downsides with mounting object storage as documented on their [README](https://github.com/s3fs-fuse/s3fs-fuse/blob/master/README.md):

- random writes or appends to files require rewriting the entire object, optimized with multi-part upload copy
- metadata operations such as listing directories have poor performance due to network latency
- non-AWS providers may have eventual consistency so reads can temporarily yield stale data (AWS offers read-after-write consistency since Dec 2020)
- no atomic renames of files or directories
- no coordination between multiple clients mounting the same bucket
- no hard links
- inotify detects only local modifications, not external ones by other clients or tools

Lets get started by installing `s3fs`:

```bash
# For Fedora
sudo dnf install s3fs-fuse
# For Ubuntu/Debian
sudo apt install s3fs
```

We'll then need to edit `/etc/passwd-s3fs` with our object storage access and secret keys:

```yaml
AccessKeyHere:SecretKeyHere
```

Then we need to set it so that only root can read `/etc/passwd-s3fs`

```bash
sudo chmod 600 /etc/passwd-s3fs
```

Now we can test to see if we can access our bucket:

```bash
sudo s3fs bucketname \
	/mnt/mountpoint \
	-o url=https://us-east-1.linodeobjects.com \
	-o allow_other
```

If we're successful we should be able to access `/mnt/mountpoint`.

To unmount:

```bash
sudo umount /mnt/mountpoint
```

To mount automatically during reboot, add the following to `/etc/fstab`:

```
bucketname /mnt/mountpoint     fuse.s3fs _netdev,allow_other,url=https://us-east-1.linodeobjects.com  0 0
```

After editing `/etc/fstab` you can run `sudo mount -a` in order for it to load and mount any new entries.

