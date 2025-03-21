---
date: 2021-03-15 22:09:38
draft: false
medium_enabled: true
medium_post_id: f742be560b7f
tags:
- Python
title: Detect Python Version
---

I was working on a distribution recently where `python` was mapped to `python2`. It mixed me up for a bit since I was writing a script for `python3` but it ran partially under `python2`. To lower confusion in the future, I think it's a great idea to check the python version and exit if it isn't the version you expect.

```python
from sys import version_info, exit

if version_info.major != 3:
    print("This script only supports Python 3")
    print("Curent version: " + \
          str(version_info.major) + "." + \
          str(version_info.minor) + "." + \
          str(version_info.micro)
    )
    print("Exiting...")
    exit(1)
```