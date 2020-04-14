---
title: "Quick Python: Concurrent Futures"
date: 2020-04-11T20:40:28-04:00
draft: false
tags: ["python", "concurrency"]
---

Another way to perform concurrency in python is to use the `concurrent.futures` module.

```python
from concurrent.futures import ThreadPoolExecutor, ProcessPoolExecutor
def add(x, y):
    return x + y
with ThreadPoolExecutor(max_workers=4) as executor:
    future = executor.submit(add, 1, 2)
    result = future.result(timeout=30) # unit: seconds
```

If `max_workers=None` then it will default to the number of processors on the machine multiplied by 5.

If `timeout=None` then there is no time limit applied.

You can also apply a function to a list or iterables

```python
def double(x):
    return 2 * x
with ThreadPoolExecutor() as executor:
    future = executor.map(function_handle, [1, 2, 3])
    result = future.result()
```

Instead of threads, it is also possible to spawn processes to side-step the global interpreter lock. The documentation warns that only picklable objects can be executed and returned though.

```python
def add(x, y):
    return x + y
with ProcessPoolExecutor() as executor:
    future = executor.submit(add, 1, 2)
    result = future.result()
```

