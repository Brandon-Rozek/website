---
title: "Quick Python: Dataclasses"
date: 2020-04-08T18:59:48-04:00
draft: false
tags: ["python"]
---

Python 3.7 and above have a feature called dataclasses. This allows us to reduce boilerplate code by removing the need to create a whole constructor and providing a sensible `__repr__` function.

```python
from dataclasses import dataclass

@dataclass
class Person:
    name: str
    age: int
```

Usage:

```python
p = Person("Bob", 30)
print(p)
```

```
Person(name='Bob', age=20)
```

