---
title: "Terminal Output in Vim"
date: 2021-06-18T16:22:30-04:00
draft: false
tags: []
medium_enabled: true
---

In Vim you can output the result of a command below your cursor by using `:r!`. 

Examples:

Hello World

```
:r! echo Hello World
```

The current timestamp

```
:r! echo "[$(date '+\%Y-\%m-\%d \%H:\%M:\%S')]"
```

Outputs: `[2021-06-18 16:13:19]`

