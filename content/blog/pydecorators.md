---
title: "Quick Python: Decorators"
date: 2020-03-30T18:07:14-04:00
draft: false
tags: ["Python"]
medium_enabled: true
---

[Geir Arne Hjelle](https://realpython.com/team/gahjelle/) at Real Python wrote a great post called [Primer on Python Decorators](https://realpython.com/primer-on-python-decorators/). I recommend reading that as this post serves mostly as a reminder to myself on how to write a decorator.

I find decorators useful for several reasons

- Check a pre-existing condition (Is the user logged in?)
- Perform post processing on function output (Convert to SI units)
- Expose extra variables for use in the function

Here is a template for how a decorator is written

```python
import functools

def decorator(func):
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        # Do something before
        value = func(*args, **kwargs)
        # Do something after
        return value
    return wrapper
```

If your decorator takes arguments then there's another layer...

```python
def decorator_with_argument(argument):
    def decorator(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            # Do something before
            value = func(*args, **kwargs)
            # Do something after
            return value
        return wrapper
    return decorator
```



## Example: Logging

Let's write a decorator that logs the string returned by the function to a file.

```python
def filelog(filename):
    def decorator(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            with open(filename, 'w') as f:
                f.write(func(*args, **kwargs))
        return wrapper
    return decorator

@filelog('log.txt')
def greet(name):
    return f"Hello {name}!"
```

