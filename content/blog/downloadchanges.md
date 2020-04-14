---
title: "Download Changes"
date: 2020-04-12T15:28:31-04:00
draft: false
tags: []
---

When testing daily ISO images, it is useful to only download the parts of the ISO that has changed since the previous days. That way we can preserve time and bandwidth. 

## Rsync method

This approach requires server-side support, and a lot of flags specified.

```bash
rsync --times \
  --compress --partial \
  --progress --stats \
  --human-readable \
  --human-readable \
  rsync://cdimage.ubuntu.com/cdimage/kubuntu/daily-live/20200412/focal-desktop-amd64.iso \
  kubuntu-focal-desktop-amd64.iso
```

| Flag               | Description                                                  |
| ------------------ | ------------------------------------------------------------ |
| `--times`          | Transfer modification times along with the files.            |
| `--compress`       | Compress the file data during transit.                       |
| `--partial`        | Keep partial downloads if interrupted.                       |
| `--progress`       | Print information showing the progress of the /transfer.     |
| `--stats`          | Print a set of statistics on the file transfer.              |
| `--human-readable` | Output numbers in a more human readable format, can use up to 3 times. |

## Zsync method

This approach does not involve adding a bunch of flags, but it does require the provider to have a `.zsync` file on their server and for the user to have the `zync` package installed. This package typically isn't installed by default on most systems.

```bash
zsync http://cdimage.ubuntu.com/kubuntu/daily-live/20200412/focal-desktop-amd64.iso.zsync
```

