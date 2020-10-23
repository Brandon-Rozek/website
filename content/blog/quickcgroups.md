---
title: "Quickly Creating CGroups to Limit CPU/Memory of Applications"
date: 2020-10-22T22:32:56-04:00
draft: false
tags: []
---

Running some data science algorithms can be CPU or memory intensive. To prevent the code from hogging system resources, we can use cgroups to set limits. This also is great for applications that you don't quite trust.

## Defining the CGroup

On Ubuntu, we will have to install `cgroup-tools`

```bash
sudo apt install cgroup-tools
```

Let's create a cgroup called `limitapp`

```bash
sudo cgcreate -a $USER -t $USER -g memory,cpu:limitapp
```

We can limit the RAM usage in this cgroup to 2GB. [According to the Arch Linux Wiki](https://wiki.archlinux.org/index.php/Cgroups#Ad-hoc_groups), this limit only applies to RAM not SWAP.

```bash
echo 2000000000 > /sys/fs/cgroup/memory/limitapp/memory.limit_in_bytes
```

All processes belong to a cgroup. The majority of them belong to what is considered the root cgroup. By default, all groups have 1024 CPU shares. The amount of shares that you define in the cgroup determines the approximate percentage of CPU time that the cgroup will get if the system is congested.

Let's say that our cgroup can have 50% of the CPU time when the system is stressed:

```bash
echo 512 > /sys/fs/cgroup/cpu/limitapp/cpu.shares
```

## Assigning Applications to CGroups

We can assign an existing application to a cgroup. For example, let us assign `firefox` to our cgroup.

```bash
cgclassify -g memory,cpu:limitapp $(pidof firefox)
```

We can start new processes in our cgroup. For example, let us start a python environment in our cgroup.

```bash
cgexec -g memory,cpu:limitapp python
```

