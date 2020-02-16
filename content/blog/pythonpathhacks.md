---
title: "Python Path Hacks"
date: 2020-01-13T22:26:16-05:00
draft: false
tags: [ "python" ]
---

There are two quick ways to hack together custom imports in Python. One is by using the `PYTHONPATH` environmental variable, and the other way is by using the `sys` module in Python.

## Method 1: `PYTHONPATH`

Before you call `python` set the environmental variable.

```bash
PYTHONPATH=$PYTHONPATH:/other/path
```

Then you can call `python`.

## Method 2: `sys`

In the beginning of your Python script add the following code.

```python
import sys
sys.path.append('/other/path')
```

## Remarks

Of course this isn't the best way to add custom libraries to your Python scripts. Ideally, we would use `pip` to manage our dependencies. Perhaps a future blog post will cover this!
