---
title: "xpra"
date: 2020-01-15T18:29:57-05:00
draft: false
tags: [ "X11" ]
medium_enabled: true
---

[`xpra`](http://xpra.org/) allows one to run persistent X applications on a remote host and display it on a local machine. It's a combination of [SSH X11 Forwarding](https://wiki.archlinux.org/index.php/OpenSSH#X11_forwarding) and [Screen](https://www.gnu.org/software/screen/).

To get started you need to install the `xpra` package on both the server and client. On Ubuntu 18.04, this package isn't configured properly so one should use this PPA instead.

```bash
sudo add-apt-repository ppa:mikhailnov/xpra
```

To install,

```bash
sudo apt install xpra
```

Now you can from the client open up an application with one command

```bash
xpra start ssh:user@host --exit-with-children --start-child="executable"
```

If you want it to behave more like screen. Then on the server.

```bash
xpra start :100
```

Where you can replace `:100` with another high display number.

Then you can run the executable,

```bash
DISPLAY=:100 executable
```

From the client,

```bash
xpra attach ssh:user@host:100
```

`xpra` has heuristics that determines the encoding of the images passed. You can however override it using the `--encoding`s flag to better tailor to your needs.

- `rgb`: Raw pixel format that is lossless and uses compression. Best in high bandwidth environments.
- `png` compressed, lossless, but CPU intensive. May result in skipped frames
- `h264`, `vp8`, `vp9` are lossy formats that have tunable quality and speed parameters


More resources:
- [Arch Wiki](https://wiki.archlinux.org/index.php/Xpra)
- [Ubuntu Wiki](https://help.ubuntu.com/community/Xpra)

