---
title: "Python asyncio"
date: 2020-04-09T16:37:41-04:00
draft: false
tags: ["Python"]
---

Daniel Pope wrote a [great blog post](http://mauveweb.co.uk/posts/2014/07/gevent-asynchronous-io-made-easy.html) describing the different ways of performing asynchronous I/O in Python. In this post, I want to focus on his section called "Generator-based Coroutine". Python's `asyncio` module in the standard library has a concept of "coroutines" that uses generators instead of callbacks or promises seen in other asynchronous frameworks. 

Whenever a I/O call is made, you can prepend the statement with `yield from` and as long as the function is under the `asyncio.coroutine` generator, the Python module will handle the call asynchronously. Now this method doesn't fully fit under the coroutine framework since generators can only yield to the caller frame. Therefore, it is called a [semicoroutine](https://en.wikipedia.org/wiki/Coroutine#Comparison_with_generators).

Here is an example of its usage

```python
import asyncio

@asyncio.coroutine
def think(duration):
    print("Starting to think for " + str(duration) + " seconds...")
    yield from asyncio.sleep(duration)
    print("Finished thinking for " + str(duration) + " seconds...")

loop = asyncio.get_event_loop()
loop.run_until_complete(asyncio.gather(
    think(5),
    think(2)
))
loop.close()
```

Output:

```
Starting to think for 5 seconds...
Starting to think for 2 seconds...
Finished thinking for 2 seconds...
Finished thinking for 5 seconds...
```

## Newer Syntax

Now the decorator syntax has been deprecated in Python 3.8 in favor of the more common `async` /`await` syntax introduced in Python 3.7.  The reason I showed the previous version is because I think it's important to understand how this module is implemented behind the scenes. Also since Python 3.6 code is likely still floating around,  you might encounter code bases like the above in your day to day.

Here is the equivalent code written in modern day syntax

```python
import asyncio

async def think(duration):
    print("Starting to think for " + str(duration) + " seconds...")
    await asyncio.sleep(duration)
    print("Finished thinking for " + str(duration) + " seconds...") 

async def main():
    await asyncio.gather(
        think(2),
        think(5)
    )

asyncio.run(main())
```

Not that much shorter in terms of lines of code, but it allows the developer to not have to be concerned about the event loop or generators.