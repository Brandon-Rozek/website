---
title: "Rsync with a Different Key"
date: 2019-07-06T09:20:05-04:00
draft: false
medium_enabled: true
---

To use Rsync with a different key, follow the command structure below.

```bash
rsync -e "ssh -i $HOME/.ssh/key" user@hostname:/from/dir/ /to/dir/
```

Though for syncing my local website to my VPS, I usually like having more options with my rsync command

```bash
rsync -Paz --delete -e "ssh -i $HOME/.ssh/key" user@hostname:/from/dir/ /to/dir/
```

Quick option definitions (from man page)

| Option         | Description                                                  |
| -------------- | ------------------------------------------------------------ |
| -e             | Allows you to override the default shell used as the transport for rsync.  Command line options are permitted after the command name. |
| -a, --archive  | This is equivalent to -rlptgoD. It is a quick way of saying you want recursion and want to preserve almost everything (with -H being a notable omission).  The only exception to the above equivalence is when --files-from is specified, in which case -r is not implied. Note that -a does not preserve hardlinks, because finding multiply-linked files is expensive.  You must separately specify -H. |
| -P             | Equivalent to --partial --progress.  Its purpose is to make it much easier to specify these two options for a long transfer that may be interrupted. |
| -z, --compress | Compress file data during the transfer                       |
| --delete       | Delete extraneous files from dest dirs                       |

