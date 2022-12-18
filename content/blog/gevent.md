---
title: "Gevent"
date: 2020-04-09T17:22:52-04:00
draft: false
tags: ["Python"]
---

In my last post I spoke about [concurrency with asyncio](/blog/pyasyncio/). Now what if you don't want to concern yourself with async/await practices and just want to write synchronous code that executes I/O asynchronously?  That's where the library [gevent](http://www.gevent.org/) comes in. It does this by modifying Python's standard library during runtime to call it's own asynchronous versions.

Last post code's example written in `gevent`.

```python
# The first two lines must be called before
# any other modules are loaded
import gevent
from gevent import monkey; monkey.patch_all()

import time

def think(duration):
    print("Starting to think for " + str(duration) + " seconds...")
    time.sleep(duration)
    print("Finished thinking for " + str(duration) + " seconds...")

gevent.wait([
    gevent.spawn(think, 5),
    gevent.spawn(think, 2)
])
```

Notice that the function `think` is written the same as the synchronous version. 

`gevent` is written on top of C libraries `libev` or `libuv` . This combined with the monkey patching can make `gevent` based applications hard to debug if something goes wrong. Otherwise it's a great tool to quickly take advantage of concurrency.