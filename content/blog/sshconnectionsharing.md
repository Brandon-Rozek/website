---
title: "SSH Connection Sharing"
date: 2020-06-05T16:39:24-04:00
draft: false
tags: ["SSH"]
medium_enabled: true
---
If you're like me, you open a lot of different terminal sessions throughout your day. When it comes to SSH, I want these different sessions to share a connection rather than creating a new one each time.

To accomplish this, I have the following in my `~/.ssh/config` file.

```
ControlMaster auto
ControlPersist no
ControlPath ~/.ssh/sockets/socket-%r@%h:%p
```

| Option           | Description                                                  |
| ---------------- | ------------------------------------------------------------ |
| `ControlMaster`  | Allows connection sharing                                    |
| `ControlPersist` | `yes` to keep connection up even when no clients are connected. `2s` (or custom timeout) to keep the connection up for 2 seconds after no clients are connected.`no` to disconnect immediately |
| `ControlPath`    | Where to store connection information. This should not be writable by other users. |


You'll also need to create the `sockets` folder if you don't have it already setup.

```bash
mkdir ~/.ssh/sockets
chmod go-w ~/.ssh/sockets
```

