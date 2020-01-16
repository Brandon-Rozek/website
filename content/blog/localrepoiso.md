---
title: "Local Repo From Live Installer"
date: 2019-08-30T20:26:53-04:00
draft: false
---

I'm going to share my experience setting up a local repo from a CentOS live CD. These instructions should work similarly in REHL.

When working with off-network systems, it is often useful to have the base packages on the system after the installation process. Luckily the base packages are commonly included in the ISO installer.

First I'm going to assume that you've mounted the ISO at `/mnt`.

```bash
sudo mkdir -p /repos/local
sudo rsync -Paz /mnt/Packages /repos/local/Packages
sudo rsync -Paz /mnt/repodata /repos/local/repodata 
```

Then create the file `/etc/yum.repos.d/local.repo`

```yaml
[local]
name=Local Repo
baseurl=file:///repos/local/
gpgcheck=0
enabled=1
```

Now you're all set to go with the packages on the Live CD!