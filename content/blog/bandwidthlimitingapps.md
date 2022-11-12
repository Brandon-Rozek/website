---
title: "Bandwidth Limiting Applications"
date: 2020-10-22T21:51:27-04:00
draft: false
tags: ["Linux", "Networking"]
---

Whether it's web scraping or testing low latency connections, we want to be able to bandwidth limit certain applications. I've written about [rate limiting network interfaces](/blog/limitbandwidth/) before. This post focuses on the application level instead.

First if the application has an option to rate limit, then we should prefer that. Here are the ways you can rate limit in some common terminal applications. Let's say you set the bandwidth limit as `$max_kbps`

```bash
rsync --bwlimit $max_kbps ...
```

```bash
curl --limit-rate $max_kbps ...
```

```bash
wget --limit-rate $max_kbps ...
```

If the application you want to rate limit does not have a convenient flag and is dynamically linked, then we can use the application [`trickle`](https://github.com/mariusae/trickle).

```bash
trickle -s -d $max_kbps -u $max_kbps
```

| Flag | Description                                |
| ---- | ------------------------------------------ |
| `-s` | Standalone Mode                            |
| `-d` | Download Bandwidth Consumption Rate (KB/s) |
| `-u` | Upload Bandwidth Consumption Rate (KB/s)   |

Trickle works by replacing the socket library that is dynamically linked. 