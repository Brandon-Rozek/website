---
title: "NotImplemented"
date: 2019-10-27T23:35:17-04:00
draft: false
tags: [ "Python" ]
---

Let's say you overwrite the `__mul__` operator in a class in Python, but you don't want the function to be called for all kinds of input. You can specify the type by just returning `NotImplemented` for types you don't want.

```python
class A:
    def __mul__(self, x):
        if not isinstance(x, A):
            return NotImplemented
        return someOperation()
```

