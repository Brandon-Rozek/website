---
title: "Quick Python: Async Callbacks"
date: 2020-07-11T20:23:29-04:00
draft: false
tags: ["Python"]
medium_enabled: true
---

I've written a post on using [callbacks in Python](/blog/pysubscribepattern/). Though to add callbacks to `asyncio` functions, you'll have to interact with the loop object directly. Replace the emit function in the previous post with the following:
```python
class Application:
    # ...
    def emit(self, message):
        for callback in self.callbacks:
            if asyncio.iscoroutine(callback):
                loop = asyncio.get_running_loop()
                loop.call_soon(
                    functools.partial(
                        asyncio.ensure_future,
                        callback(message)
                    )
                )
            else:
                callback(message)
```
