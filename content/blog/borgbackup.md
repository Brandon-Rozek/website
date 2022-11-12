---
title: "Borg Backup"
date: 2019-05-21T22:35:31-04:00
draft: false
tags: ["Backup"]
---

I started using [Borg Backup](https://www.borgbackup.org/) in order to efficiently and securely do my backups. I did some research before choosing this solution as I required three things:

- Compression
- Encryption
- Deduplication

Each point is important on their own. Ideally I would be able to put this onto a cloud solution. Due to this I would want compression and deduplication to keep my costs down and encryption in order to maintain privacy.

Luckily Borg does all of these things and more! It's also easily available on the AUR and the Ubuntu repositories.

## Getting Started

This will be a short post just describing the basic usage of the tool. I haven't fully implemented this tool yet so forgive me if this doesn't match your exact use case. This is also a great way for me to document the basic commands for myself as well.

First to initialize a borg repo encrypted with a password at `repolocation`:

```bash
borg init --encryption=repokey repolocation
```

Then to create a backup in the repo with key `backup1`:

```bash
borg create --stats --progress --compression lzma repolocation::backup1 folderToBackup
```

You can actually replace the compression algorithm if wanted, here is a short description from their [website](https://borgbackup.readthedocs.io/en/stable/):

- lz4 (super fast, low compression)
- zstd (wide range from high speed and low compression to high compression and lower speed)
- zlib (medium speed and compression)
- lzma (low speed, high compression)

To list what backups you have in the repo:

```bash
borg list repolocation
```

To mount and unmount the repository

```bash
borg mount repolocation mountlocation
```

```bash
borg umount mountlocation
```

