---
title: "Quick Python: Copy Decorator"
date: 2020-04-08T18:49:54-04:00
draft: false
tags: ["Python"]
medium_enabled: true
---

If you want to guarantee that your function doesn't modify any of the references and don't mind paying a price in memory consumption, here is a decorator you can easily add to your functions.

```python
from copy import deepcopy
def copy_arguments(func):
    def wrapper(*args, **kwargs):
        new_args = deepcopy(args)
        new_kwargs = deepcopy(kwargs)
        return func(*new_args, **new_kwargs)
    return wrapper
```

Example usage:

```python
@copy_arguments
def modify1(xs):
    for i, _ in enumerate(xs):
        xs[i] *= 2
```

Comparison:

```python
def modify2(xs):
    for i, _ in enumerate(xs):
        xs[i] *= 2

a = [1, 2, 3, 4, 5]
b = [1, 2, 3, 4, 5]
modify1(a)
modify2(a)
print(a)
print(b)
```

```
[1, 2, 3, 4, 5]
[2, 4, 6, 8, 10]
```

