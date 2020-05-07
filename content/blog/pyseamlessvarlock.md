---
title: "Quick Python: Seamless Variable Locks"
date: 2020-05-06T23:01:39-04:00
draft: false
tags: ["python", "concurrency"]
---

Combining Python's [Getters and Setters](https://brandonrozek.com/blog/pygetset/) with locks can give us seamless thread-safe variable access.

```python
from threading import Lock
class Person:
    def __init__(self):
        self._age = 0
        self.age_lock = Lock()
    @property
    def age(self):
        a = None
        with self.age_lock:
            a = self._age
        return a
    
    @age.setter
    def age(self, a):
        with self.age_lock:
            self._age = a
```

