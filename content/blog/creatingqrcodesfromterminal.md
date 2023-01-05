---
title: "Creating QR Codes from the Terminal"
date: 2020-09-26T22:13:25-04:00
draft: false
tags: []
medium_enabled: true
---

With the tool `qrencode`, it is surprisingly simple to create a QR code. 

```bash
echo "https://brandonrozek.com" | qrencode -t ansiutf8
```

![](/files/images/blog/20200926221423.png)
