---
title: "Launch Apps through the Terminal"
date: 2020-09-26T21:48:09-04:00
draft: false
tags: []
---

Normally when you launch an application through the terminal, the standard output appears, and closing the terminal closes the application. The `nohup` command allows applications to run regardless of any hangups sent. Combine that with making it a background task, and you have a quick and easy way to launch applications through the terminal.

```bash
nohup application > /dev/null &
```

