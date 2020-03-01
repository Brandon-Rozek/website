---
title: "SSH Jump"
date: 2020-02-02T22:32:13-05:00
draft: false
tags: [ "SSH" ]
---

With ssh jump, we can ssh into a machine that we don't have direct access to through an intermediary.

Just chain the necessary hosts together with the following command:

```bash
ssh -J host1 host2 host3 ...
```

Where the last host is the one you wish to connect to at the end.

Luckily ssh config also supports this!

```
Host host1
  HostName host1.example.com

Host host2
  HostName hidden.host1.example.com
  ProxyJump host1
```

