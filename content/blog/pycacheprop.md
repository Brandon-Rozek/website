---
title: "Quick Python: Cached Property"
date: 2020-04-18T18:29:21-04:00
draft: false
tags: ["python"]
---

If you have a property in an object that only needs to be computed once, consider using `cached_property` to store the result and serve for future function calls.

```python
import functools
class Number:
    def __init__(self, n):
        self.n = n
    @functools.cached_property
    def is_prime(self):
    	return all(self.n % i for i in range(2, self.n))
```

Let's test it with the Mersenne prime `524287`.

```python
n = Number(524287)
n.is_prime
```

After maybe 1-2 seconds of thinking you should get `True.`

Run it again and the result will be instantaneous!