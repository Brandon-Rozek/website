---
title: "Launch Apps through the Terminal"
date: 2020-09-26T21:48:09-04:00
draft: false
tags: ["Linux"]
---

Normally when you launch an application through the terminal, the standard output appears, and closing the terminal closes the application.

## Using `systemd`

[Tem Tem](https://fosstodon.org/@ralismark) recently [tooted](https://fosstodon.org/@ralismark/108266728217245129)
a [blog post](https://www.ralismark.xyz/posts/systemd-run) they wrote on replacing `nohup` with `systemd-run`


To run a graphical application it's as easy as:
```bash
systemd-run --user application
```

If you want to see any of the application terminal output,
then when the service is running you can check the status
like any other systemd service.
```bash
systemd --user status application
```

Note that the current directory information is not known
to `systemd-run`. Therefore, if you'll need to specify
absolute as opposed to relative paths. For example:
```bash
systemd-run --user okular "$PWD/document.pdf"
```

Check out Tem Tem's [blog post](https://www.ralismark.xyz/posts/systemd-run) for more on `systemd-run`!


## Using `nohup` (Legacy)

When the terminal closes, it sends a hangup signal to all of the processes it manages.
The `nohup` command allows applications to run regardless of any hangups sent.
Combine that with making it a background task,
and you have a quick and easy way to launch applications through the terminal.

```bash
nohup application > /dev/null &
```

