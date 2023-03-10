---
date: 2020-12-20 01:15:24
draft: false
medium_enabled: true
medium_post_id: c7a65890d9d9
tags:
- Bash
- Networking
title: 'Quick Bash: Validate IP Address'
---

`ipcalc` is a terminal tool that lets you validate an IP address. This proves useful to me as I have scripts that automate certain remote tasks given an IP address. Instead of trusting that an argument passed is a valid IP, why not check it?

First the script would need to check if `ipcalc` exists.

```bash
if ! command -v ipcalc > /dev/null ; then
    echo "ipcalc not found. Exiting..."
    exit 1
fi
```

Now for this example, we'll validate an IP address stored in the variable `$IP`.

```bash
if ! ipcalc -cs "$IP" ; then
    echo "Invalid IP Address"
    exit 1
fi
```