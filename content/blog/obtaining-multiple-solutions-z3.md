---
date: 2022-12-31 09:52:00-05:00
draft: false
math: true
medium_enabled: true
medium_post_id: d4f11c04d852
tags:
    - Formal Methods
title: Obtaining Multiple Solutions Z3
---

Playing around with Diophantine solvers, I wanted to obtain the solutions of the following equation:
$$
5a + 4b - 3c = 0
$$
Let's encode that using Z3

```python
from z3 import *

# Encode Equation
a, b, c = Ints("a, b, c")
s = Solver()
s.add(5 * a + 4 * b - 3 * c == 0)

# Find solution
result = s.model()
if result == sat:
    print(result)
```

This code snippet returns

```
[a = 0, b = 0, c = 0]
```

Now there are multiple solutions to this Diophantine equation, so how do we get the others? It turns out after searching around StackOverflow (see references) the only way is to add the previous solutions as constraints.

```python
# This encodes the last solution as a constraint
block = []
for var in m:
    block.append(var() != m[var])
s.add(Or(block))
```

Formulaically, this corresponds to: 
$$
a \ne 0 \vee b \ne 0 \vee c \ne 0
$$
If you look at the references, it's hard to encode these constraints generally. This is because Z3 is a powerful SMT solver working with many different theories.  Though if we restrict ourselves to the Diophantine equations, we can write a function that acts as a generator for all of the solutions:

```python
import z3

def get_solutions(s: z3.z3.Solver):
    result = s.check()
    # While we still get solutions
    while (result == z3.sat):
      m = s.model()
      yield m
      # Add new solution as a constraint
      block = []
      for var in m:
          block.append(var() != m[var])
      s.add(z3.Or(block))
      # Look for new solution
      result = s.check()
```

Now for our example, this allows us to do the following:

```python
from z3 import *

a, b, c = Ints("a, b, c")
s = Solver()
s.add(5 * a + 4 * b - 3 * c == 0)

solutions = get_solutions(s)
upper_bound = 10
for solution, _ in zip(solutions, range(upper_bound)):
    print(solution)
```

The solutions of a linear Diophantine equation can be easily parameterized so I don't recommend using Z3 in this way. Though I think this exercise is informative for other theories you might be trying to satisfy. 

## References

- https://stackoverflow.com/questions/11867611/z3py-checking-all-solutions-for-equation/70656700#70656700
- https://stackoverflow.com/questions/11867611/z3py-checking-all-solutions-for-equation/70656700#70656700
- https://stackoverflow.com/questions/63231398/trying-to-find-all-solutions-to-a-boolean-formula-using-z3-in-python/63232953#63232953