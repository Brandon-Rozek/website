---
title: "Quick Python: Memoization"
date: 2020-03-30T17:31:55-04:00
draft: false
tags: ["python"]
---

There is often a trade-off when it comes to efficiency of CPU vs memory usage. In this post, I will show how the [`lru_cache`](https://docs.python.org/3/library/functools.html#functools.lru_cache) decorator can cache results of a function call for quicker future lookup.

```python
@lru_cache(maxsize=2**7)
def fib(n):
    if n == 1:
        return 0
    if n == 2:
        return 1
    return f(n - 1) + f(n - 2)
```

In the code above, `maxsize` indicates the number of calls to store. Setting it to `None` will make it so that there is no upper bound. The documentation recommends setting it equal to a power of two.

Do note though that `lru_cache` does not make the execution of the lines in the function faster. It only stores the results of the function in a dictionary.