---
title: "Mirror Download with wget"
date: 2020-01-20T21:18:12-05:00
draft: false
tags: [ "linux", "archive" ]
---

This post will describe downloading a `centos` repo using `wget`. Though the ideas in this blog post can apply to any mirror with packages exposed via http.

```bash
wget \
  --accept rpm,bz2,gz,xml,asc \
  --recursive \
  --no-parent \
  --no-host-directories \
  --cut-dirs=4 \
  http://mirror.centos.org/centos/8/BaseOS/x86_64/os/ 
```

Here are what the options mean...

| Option                  | Meaning                                                      |
| ----------------------- | ------------------------------------------------------------ |
| `--accept`              | Comma separated by which extensions to allow downloading     |
| `--recursive`           | Follow links                                                 |
| `--no-parent`           | Only follow links that are sub-directories of the current one |
| `--no-host-directories` | Exclude creating a folder indicating the hostname            |
| `--cut-dirs=N`          | Don't make folders for a depth of `N` subdirectories. Notice in the example `centos`, `8`, `BaseOS`, `x86_64`, `os` is a list of 5 subdirectories so `N`=5 |

