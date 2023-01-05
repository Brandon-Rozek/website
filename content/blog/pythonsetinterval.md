---
title: "Python: Set Interval"
date: 2020-02-25T21:34:03-05:00
draft: false
tags: [ "Python" ]
medium_enabled: true
---

Javascript has a function called `setInterval` which given a length of time $T$ and a callback function, it will perform that function every $T$ milliseconds. For example, to print "Hello, World!" every 5 seconds:

```javascript
setInterval(function() {
    console.log("Hello, World!")
}, 5 * 1000)
```

Wouldn't it be nice if Python had a similar functionality? Well thanks to [right2clicky](https://stackoverflow.com/a/48741004), there's a nice and quick way to implement one.

```python
from threading import Timer

class Repeat(Timer):
    def run(self):
        while not self.finished.wait(self.interval):
            self.function(*self.args, **self.kwargs)
```

Since `self.finished.wait` only returns `True` when the Event `self.finished` is set to true, the thread will keep waiting and calling the function for the set interval time period.

The same post has a usage example:

```python
from time import sleep

t = Repeat(1.0, lambda: print("Hello, World!"))
t.start()
sleep(5)
t.cancel()
```

