---
title: "Quick Python: Export Decorator"
date: 2020-06-14T22:15:38-04:00
draft: false
tags: []
---

A great [StackOverflow post](https://stackoverflow.com/a/35710527) by [Aaron Hall](https://stackoverflow.com/users/541136/aaron-hall) that shows how you can create an `export` decorator in order to not have to specify all the names you want to expose via [`__all__`](https://brandonrozek.com/blog/pythonall/).

The Decorator:

```python
import sys

def export(fn):
    mod = sys.modules[fn.__module__]
    if hasattr(mod, '__all__'):
        mod.__all__.append(fn.__name__)
    else:
        mod.__all__ = [fn.__name__]
    return fn
```

Usage:

```python
__all__ = []

@export # otherwise __all__ = ['test']
def test():
    print("test")
```

