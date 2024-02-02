---
title: "Quick Python: Refactoring Exceptions with Context Manager"
date: 2024-02-01T20:48:21-05:00
draft: false
tags: ["Python"]
math: false
medium_enabled: false
---

I generally find exception syntax a little clunky...

```python
try:
    for _ in range(5):
        sleep(1)
except KeyboardInterrupt:
    # Awesome task 1
    # Awesome task 2...
    pass
```

Especially if you end up capturing the same exceptions and handling it the same way.

```python
try:
    for _ in range(5):
        sleep(1)
except KeyboardInterrupt:
    # Awesome task 1
    # Awesome task 2...
    pass

try:
    for _ in range(2):
        sleep(1)
except KeyboardInterrupt:
    # Awesome task 1
    # Awesome task 2...
    pass
```

One way to make our code more DRY (don't-repeat-yourself) is to make use of Python's context managers.

```python
@contextmanager
def handle_sigint():
    try:
        yield
    except KeyboardInterrupt:
        # Awesome task 1
        # Awesome task 2...
        pass
```

Using the context manager, everything within the indented block gets executed within the try block.

```python
with handle_sigint():
    for _ in range(5):
        sleep(1)

with handle_sigint():
    for _ in range(2):
        sleep(1)
```

In fact, we can write this in a generic way to give us an alternative syntax for handling exceptions.

```python
@contextmanager
def handle_exception(f, *exceptions):
    try:
        yield
    except exceptions as e:
        f(e)
```

For example, let's tell the user that we're explicitly ignoring their exception

```python
def ignore(e):
    print("Ignoring", e.__class__.__name__)

with handle_exception(ignore, NotImplementedError, KeyboardInterrupt):
    for _ in range(5):
        sleep(1)
```

