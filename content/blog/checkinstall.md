---
title: "Checkinstall"
date: 2020-04-26T12:11:30-04:00
draft: false
tags: ["Packaging", "Linux"]
medium_enabled: true
---

To create a quick and dirty Debian or RPM package, check out `checkinstall`! Be forewarned though that this isn't the recommended way of creating packages. This post on [AskUbuntu](https://askubuntu.com/questions/1138384/why-is-checkinstall-no-longer-being-maintained) gives good reasons for why. Though if it is between running a `make install` or running this utility, I would consider running `checkinstall` instead.

This program works by tracking all the files installed by a `make install` equivalent. This makes it easy to remove later on. 

To install on a debian based distribution,

```bash
sudo apt install checkinstall
```

Then you can go to the directory that you normally `make install` and instead run the following to make a Debian package.

```bash
sudo checkinstall -D --install=no --nodoc
```

It will ask you to fill in various metadata such as name and author, and then it will create a package you can install!

To install,
```bash
sudo dpkg -i filename.deb
```

You can later remove it with apt.

```bash
sudo apt remove package_name
```

If the application does not use `make install`, then you can add extra arguments to denote its equivalent

```bash
sudo checkinstall -D --install=no --nodoc ./customInstallScript
```

Arguments to `checkinstall`

| Flag           | Description                         |
| -------------- | ----------------------------------- |
| `-D`           | Create a Debian package             |
| `-R`           | Create a RPM package                |
| `-S`           | Create a Slackware package          |
| `--install=no` | Don't install package               |
| `--nodoc`      | Do not include documentation filesq |
