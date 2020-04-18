---
title: "Quick Python: HTTP Server"
date: 2020-04-18T17:15:09-04:00
draft: false
tags: []
---

You can use Python to quickly spin up a HTTP server. A common use case for me is to quickly transfer files to mobile devices in my internal network. 

```python
python -m http.server
```

This will likely start an HTTP server on port 8000 on your machine listening to all network interfaces.