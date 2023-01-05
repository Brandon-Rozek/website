---
title: "Pip Config"
date: 2020-04-10T11:56:19-04:00
draft: false
tags: ["Python"]
medium_enabled: true
---

If you find yourself added flags to every pip command, consider adding those flag's to a pip configuration file.

In order of importance, the configuration files will be located

- Inside the virtualenv `/path/to/virtualenv/pip.conf`
- In the user folder `~/.config/pip/pip.conf`
- Site-wide `/etc/pip.conf`

It is structured as an INI file where the blocks are the commands (`global` indicates all commands) 

For an example, we can set the timeout for all commands to 60 seconds,  but the timeout for the freeze command to only 10 seconds.

```ini
[global]
timeout = 60

[freeze]
timeout = 10
```

Boolean flags are set by assigning a value of `true` or `yes` to them

```ini
[install]
ignore-installed = true
```

For operating in an offline environment,

```ini
[global]
no-index = true
find-links = /path/to/wheels
```

