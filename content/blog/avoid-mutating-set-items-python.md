---
title: "Avoid Mutating Items within a Set (Python Edition)"
date: 2023-05-17T20:46:33-04:00
draft: false
tags: ["Python"]
math: false
medium_enabled: false
---

Whenever we create a set of objects, there's an implicit assumption that those objects don't change. What happens when we break this implicit contract and mutate items within a set? If negative properties occur, how can we get around this issue? We'll explore this through the lens of set membership and talk about how the hash method and equality method are used within sets.

**Example**

We start by defining a Person class that holds a name

```python
class Person:
    def __init__(self, name):
        self.name = name
```

In order to put it within a set, we need to define a hash method.

```python
class Person:
    def __init__(self, name):
        self.name = name
    def __hash__(self):
        return hash(("Person", self.name))
    
people = {
    Person("Brandon"),
    Person("Clare"),
    Person("James"),
    Person("John")
} 
```

The property we'll focus on in this post is set membership. In other words, does the set contain a specified object? 

```python
print(Person("Brandon") in people) # False
```

This might seem strange since we can clearly see a `Person("Brandon")` in the set! The problem is that we didn't override the `__eq__` method within the class. Currently it only considers two `Person` objects the same if they share the same *reference*.

To test `Person` equivalence in a more intuitive way, we'll say that two `Person` objects are equivalent if they share the same name.

```python
class Person:
    def __init__(self, name):
        self.name = name
    def __hash__(self):
        return hash(("Person", self.name))
   	def __eq__(self, other):
        return isinstance(other, Person) and self.name == other.name
```

```python
print(Person("Brandon") in people) # True
```

Now let's mutate the names so they all start with `Awesome `

```python
for p in people:
    p.name = "Awesome " + p.name
```

Let's test for membership again

```python
print(Person("Awesome Brandon") in people) # False
print(Person("Brandon") in people) # False
```

What happened? Why is both `Awesome Brandon` and `Brandon` not in the set? This has to do with the way that the sets keep track of the objects within them. 

When an object is inserted, it's placed into bins according to their hash. Therefore, when checking for set membership, we look to see if there are items within that hash bin.

Originally when we added `Person("Brandon")` the following hash is computed:

```python
print(hash(("Person", "Brandon"))) # 8879556234447129293
```

The object `Person("Brandon")` is then placed in bin 8879556234447129293.

When we mutate the object, we don't remove the item from the set and add it back in with a recomputed hash. Instead the mutated object stays within the same hash bin.

So what happens then when we ask if `Person("Awesome Brandon")` is within the set? First, it checks to see if there are any non-empty bins with the same hash.

```python
print(hash(("Person", "Awesome Brandon"))) # 8677222781184413080
```

Our set contains no items within the 8677222781184413080 hash bin. Therefore, the set membership will immediately fail disregarding completely the `__eq__` method we define.

**Aside:** Another implicit contract we have is that for a given hash method, two equivalent objects always produce the same hash. What happens when that's not the case?

```python
import random

class Person:
    def __init__(self, name):
        self.name = name
    def __hash__(self):
        # Add randomness!
        return hash(("Person", self.name, random.randint(0, 5)))
    def __eq__(self, other):
        return isinstance(other, Person) and self.name == other.name
    def __str__(self):
        return f"Person(name={self.name})"


people = {
    Person("Brandon"),
    Person("Clare"),
    Person("James"),
    Person("John")
}

print(Person("Brandon") in people) # False
```

Again, the set membership returns false disregarding our `__eq__` method since the `__hash__` outputs don't match.

**Workaround:** If we can't mutate the items in a set directly, what should we do instead? The solution here is to remove the old items and insert newly created items with the modified data.

```python
people = {
    Person("Brandon"),
    Person("Clare"),
    Person("James"),
    Person("John")
}

to_remove = set()
to_add = set()
for p in people:
    to_remove.add(p)
    to_add.add(Person("Awesome " + p.name))

people = (people - to_remove).union(to_add)

print(Person("Awesome Brandon") in people) # True
```
