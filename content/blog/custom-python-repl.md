---
title: "Custom Python REPL"
date: 2019-10-27T23:43:12-04:00
draft: false
---

Are you tired of importing the same libraries and setting up the same variables? Why not just create your own custom REPL? Now of course, we're not going to do it from scratch, but instead utilize what Python already gives us.

Key Ingridient:

```bash
python -i prompt.py
```

This tells Python to run prompt.py and then take you into an interactive prompt.

Now let's populate `prompt.py`

```python
#!/bin/env python
import favorite_libraries

print("Welcome to your own custom REPL!")
print("Type help('function_name') to get a more detailed description on some of your own custom functions!")

def help(function_name):
    if function_name is "help":
        print("Your very own help tool!")
    else:
        print("Sorry we don't have a help written for that yet :(")
```

