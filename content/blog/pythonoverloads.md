---
title: "Python Operator Overloads"
date: 2020-03-13T20:49:28-04:00
draft: false
tags: ["Python"]
---

I wrote a [blog post about operator overloads](https://brandonrozek.com/blog/cppoverloads/) in C++. Luckily for Python it is heavily document in what is called the [Python Data Model](https://docs.python.org/3/reference/datamodel.html). Though for the sake of having content, I'll share some of the ones that I heavily use in my classes.

| Operator | Method                 |
| -------- | ---------------------- |
| `+`      | `__add__(self, other)` |
| `==`     | `__eq__(self, other)`  |
| `len()`  | `__len__(self)`        |
| `str()`  | `__str__(self)`        |
| `hash()` | `__hash__(self)`       |

Example Usage:

```python
class Test:
	def __init__(self, x):
        self.x = x
    def __add__(self, other):
        return Test(self.x, other.x)
    def __eq__(self, other):
        return self.x == other.x
    def __len__(self):
        return len(self.x)
    def __str__(self):
        return self.x
    def __hash__(self):
        return hash(self.x)
```

