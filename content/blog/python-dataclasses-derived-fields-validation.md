---
title: "Python Dataclasses: Derived Fields and Validation"
date: 2024-01-15T11:02:21-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

Python dataclasses provide a simplified way of creating simple classes that hold data.

```python
from dataclasses import dataclass

@dataclass
class Person:
    name: str
    birth_year: int
```

The above code is equivalent to:

```python
class A:
    def __init__(name: str, birth_year: int):
        self.name = name
        self.birth_year = birth_year
        self.__post__init__()
```

Notice the call to `__post__init__` at the end. We can override that method to do whatever we'd like. I have found two great use cases for this.

## Use Case 1: Derived Fields

Straight from the [Python documentation](https://docs.python.org/3/library/dataclasses.html#dataclasses.__post_init__), this use case is for when we want to use some variables to create a new variable.

For example, to compute a new field `age` from a person's `birth_year`:

```python
class Person:
    name: str
    birth_year: int
    age: int = field(init=False)
    
    def __post_init__(self):
        # Assuming the current year is 2024 and their birthday already passed
        self.age = 2024 - self.birth_year
```

## Use Case 2: Validation

Another use case is to make sure
that the user instantiates the fields
of a data class in a way we expect.


```python
class Person:
    name: str
    birth_year: int
    
    def __post__init__(self):
        assert self.birth_year > 0
        assert isinstance(self.name, str)
```


Nothing is stopping us from combining both of these use cases within the `__post_init__` method!

