---
title: "Z3 Constraint solving"
date: 2021-06-18T00:53:20-04:00
draft: false
tags: []
---

I've been looking for an easy to use constraint solver for a while and recently I've landed on using the python bindings for the SMT solver Z3.

To install:

```bash
pip install z3-solver
```

Let's say you want to find non-negative solutions for the following Diophantine equation:
$$
9x - 100y = 1
$$
To do that, we import Z3, declare our integer variables, and pass it into a solve function:

```python
from z3 import *
x, y = Ints("x y")
solve(9 * x - 100 * y == 1, x >= 0, y >= 0)
```

This will print out: `[y = 8, x = 89]`

If you want to use these values for later computations, you'll have to setup a Z3 model:

```python
from z3 import *
x, y = Ints("x y")
s = Solver
s.add(9 * x - 100 * y == 1)
s.add(x >= 0)
s.add(y >= 0)

s.check()
m = s.model()
x_val = m.eval(x)
y_val = m.eval(y)
```

