---
title: "Quick Python: Abstract Classes"
date: 2020-01-26T18:40:03-05:00
draft: false
tags: [ "python" ]
---

You can create an abstract class in Python by inheriting Abstract Base Class (`ABC`) and declaring relevant methods abstract.

First import the following from the standard library,

```python
from abc import ABC, abstractmethod
```

Then create an abstract class, making sure to add the decorator `@abstractmethod` to the constructor. This prevents the user from instantiating the class.

```python
class Animal(ABC):
    @abstractmethod
    def __init__(self, name):
        self.name = name
    @abstractmethod
    def is_bipedal(self):
        pass
    def speak(self):
        return "Hello my name is " + self.name + " and I am a " + type(self).__name__
```

In the example above:

- A constructor is made, however, the class Animal cannot be instantiated. Do note that child classes can call the constructor.
- `is_bipedal` is an abstract method that needs to be defined in child classes. `pass` indicates that it is not implemented.
- `speak` is a normal method that will be inherited by child classes.

Now let's look at a class that inherits `Animal`.

```python
class Dog(Animal):
    def __init__(self, name, owner):
        super().__init__(name) # Calls Animal constructor
        self.owner = owner
    def is_bipedal(self):
        return False
```

