---
date: 2021-06-18 20:22:30
draft: false
medium_enabled: true
medium_post_id: fba948955d22
tags: []
title: Terminal Output in Vim
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