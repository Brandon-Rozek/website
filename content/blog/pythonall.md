---
title: "Quick Python: __all__"
date: 2020-05-01T00:53:46-04:00
draft: false
tags: ["python"]
---

Anything that is defined inside a package that is imported is also brought into that workspace. So for example, if package `A` uses `numpy` and you import `A`, then `A.numpy` will be shown in your workspace. In order to limit the variables exported, you can define the ones you want to be shown in a variable called `__all__`.

Inside your package `test.py`

```python
hidden_variable = 5
shown_variable = 2
__all__ = ['shown_variable']
```

Then if you open the standard Python REPL and import `test`, only the variable `shown_variable` will be seen.

