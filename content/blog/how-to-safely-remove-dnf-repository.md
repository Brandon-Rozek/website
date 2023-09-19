---
title: "How to Safely Remove a DNF Repository"
date: 2023-09-19T15:49:30-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

After a major upgrade of Fedora or CentOS, we can be left with an outdated third-party vendor repository. Now maybe we went ahead and added the newer version of that repository, but how do we safely remove the old one?

First, we need to identify the repo id that we wish to remove.

```bash
dnf repolist
```

Example output:

```
repo id                          repo name
fedora                           Fedora 38 - x86_64
fedora-cisco-openh264            Fedora 38 openh264 (From Cisco) - x86_64
fedora-modular                   Fedora Modular 38 - x86_64
updates                          Fedora 38 - x86_64 - Updates
updates-modular                  Fedora Modular 38 - x86_64 - Updates
ancient-repo                     Fedora 1
```

We can remove all the packages from the repo id `ancient-repo` with the following command:

```bash
dnf repository-packages ancient-repo remove
```

Use this opportunity to double check that what it's going to remove is okay for your system. Some applications may not have newer versions in the other repositories, so you might have to hunt those down separately.

Also keep in mind, that this command will uninstall any unused dependencies from other repositories as well.

After removing the packages within the deprecated repository, we can remove it from the repo list.

```bash
rm /etc/yum.repos.d/ancient-repo.repo
```

Replacing `ancient-repo` with your repo id.
