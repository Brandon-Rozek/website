---
title: "Quick Python: Getters and Setters"
date: 2020-04-08T18:15:21-04:00
draft: false
tags: ["Python"]
medium_enabled: true
---

One of the hidden gems in Python classes are seamless getters and setters. I discovered this through the book [Effective Python by Brett Slatkin](https://effectivepython.com/). Though the example I'll use is different and shorter than the one he uses in his book.

Let's create a class representing a person. The only information we're going to store is their age and we'll make it optional to provide it.

```python
class Person:
    def __init__(self, age=None):
        self._age = None
    @property
    def age(self):
        if self._age is None:
            raise ValueError("age must be set before accessing it.")
        return self._age
   	@age.setter
    def age(self, age):
        if age < 0:
            raise ValueError("age must be at least zero.")
        self._age = age
```

The second function in the class decorated by `@property` will be the getter function for the attribute `_age`. The name of the function will be what we expect the user to access it as. The setter is then decorated with `age.setter` where `age` is the name of the attribute. As such the name chosen in the getter function name, setter function name, and decorator must all match.

Now let's try using it

```python
bobby = Person()
bobby.age
```

```
Traceback (most recent call last):
  File "<stdin>", line 1, in <module>
  File "/home/user/test.py", line 7, in age
    raise ValueError("age must first be set before accessing it")
ValueError: age must first be set before accessing it
```

```python
bobby.age = 5
bobby.age
```

```
5
```

