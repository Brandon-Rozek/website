---
title: "LXD on tmpfs"
date: 2019-12-31T22:35:21-05:00
draft: false
images: []
---

Container images are designed to be as small as possible. Wouldn't it be cool if we can hold entire containers in RAM? This post outlines how to accomplish this using LXD. It turns out that it is a lot easier to setup custom storage pools on LXD than with Docker.

## Setting up tmpfs

`tmpfs` is a temporary filesystem that resides in memory. To get started, first create a directory that you want to mount with `tmpfs`

```bash
mkdir /tmp/ramdisk
```

To only do this temporarily, then you can run the following command

```bash
sudo mount -t tmpfs -o size=4G myramdisk /tmp/ramdisk
```

You can replace `4G` with any size less than your current RAM size.

To set it up permanently, you will have to edit `/etc/fstab`

```
myramdisk  /tmp/ramdisk  tmpfs  defaults,size=3G,x-gvfs-show  0  0
```

## Setting up LXD

LXD is a lightweight container hypervisor in Linux. To install and setup, please follow the beginning sections of https://linuxcontainers.org/lxd/getting-started-cli/

Once you've setup the initial configuration with `lxd init`, we can create a new storage pool using our newly created `tmpfs`

```bash
lxc storage create tmplabel dir source=/tmp/ramdisk 
```

We can then create a container that will use this storage pool

```bash
lxc launch ubuntu:18.04 mycontainer -s tmplabel
```

In the last command, the `-s` flag indicates which storage pool we want to use.

With this, our entire container filesystem lives in RAM!

## (Optional) Setting up mounts

One downside to putting the entire filesystem in RAM is that it isn't persistent across reboots. You can think of the container then as ephemeral and setup mountpoints to the host in order to save important configuration information.

If the mount point is configured to be world writable or you only need it to be readonly, then this is very simple to setup!

```bash
lxc config device add mycontainer dirlabel disk source=/path/on/host path=/path/on/container
```

This is because files in the container are marked as `nobody:nogroup`. If you want to be able to write to the mounted directory that's not setup to be world-writable then there's extra steps we need to take. 

Most of the following information is taken from: https://tribaal.io/nicer-mounting-home-in-lxd.html

Let's say that you want LXD to be able to write to a folder that you own. First we need to allow LXD to remap your user ID.

```bash
echo "root:$UID:1" | sudo tee -a /etc/subuid /etc/subgid
```

We only need to do this once per host system.

The Ubuntu container has a user called `ubuntu` with UID 1000. We can remap that userid, otherwise you would have to create another user on the container to remap.

If you create another user, make sure you get its id for the next command:

```bash
# In the container
id -u username
```

For the rest of this tutorial, we will assume that you have a user named ubuntu with UID 1000.

Once LXD is able to remap your user id, you can tell it to do so for the container of interest.

```bash
lxc config set mycontainer raw.idmap "both $UID 1000"
```

Now to setup the mount

```bash
lxc config device add myubuntu homedir disk source=$HOME path=/home/ubuntu
```

Restart the container and now the `ubuntu` user will be able to write to the mount!

```bash
lxc restart mycontainer
```

