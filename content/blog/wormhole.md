---
title: "Wormhole"
date: 2019-11-20T21:21:23-05:00
draft: false
tags: [ "Linux" ]
---

A dead simple way to send files between two Linux machines not on the same network is to use a utility called [Magic Wormhole](https://github.com/warner/magic-wormhole). It is typically included in the standard repositories and is so simple the this blog post is going to end soon.

**Send a file:**

```bash
wormhole send filename 
```

This will generate a code for you to share like `6-speculate-allow`

**Receive a file:**

```bash
wormhole receive 6-speculate-allow
```

Done.

You can also rest in the fact that your data is secured by a [Password-Authenticated Key Agreement (PAKE)](https://en.wikipedia.org/wiki/Password-authenticated_key_agreement).

