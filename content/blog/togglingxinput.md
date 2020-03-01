---
title: "Toggling X Input"
date: 2020-01-07T20:46:32-05:00
draft: false
tags: [ "linux", "X11" ]
---

On X, we can easily enable or disable input devices using the `xinput` command. This is a great use case when you're tired of accidentally hitting the red Thinkpad nub or having your palm be recognized when drawing with a pen.

Running the `xinput` command performs the action temporarily. Your default settings will be restored upon a reboot.

To list `xinput` devices run:

```bash
xinput
```

To disable a device:

```bash
xinput disable [id]
```

To enable a device:

```bash
xinput enable [id]
```

The ids are listed when you list the devices.
