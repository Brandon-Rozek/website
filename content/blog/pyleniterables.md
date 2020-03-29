---
title: "Quick Python: Length of Iterables"
date: 2020-03-25T18:28:09-04:00
draft: false
tags: ["python"]
---

I wanted to find the length of what I know is a finite iterable. Normally you would think of using the `len` function but it does not work in this case. [Al Hoo](https://stackoverflow.com/a/44351664) on StackOverflow shared a quick snippet to calculate this.

```python
from functools import reduce

def ilen(iterable):
    return reduce(lambda sum, element: sum + 1, iterable, 0)
```

This also turns out to be memory efficient since we are only loading in one object into memory from the iterable at a time.