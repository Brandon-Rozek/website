---
title: "Python Patterns: Subscribe"
date: 2020-04-14T07:53:46-04:00
draft: false
tags: ["Python"]
---

It is common for larger applications to have modules that publishes and subscribes to events. This post will outline a couple ways to achieve this using [decorators](/blog/pydecorators/) and standard methods.

## Single Event

First let us concern ourselves with a single event since that's the easiest. Here we will create an application class that stores callbacks of functions through the subscribe decorator. Calling `emit` will send a message to all the functions stored in `self.callbacks`.

```python
from typing import Callable, List
class Application:
    def __init__(self):
        self.callbacks: List[Callable] = []
    def subscribe(self, func: Callable):
        if not callable(func):
            raise ValueError("Argument func must be callable.")
        self.callbacks.append(func)
        return func
    def emit(self, message):
        for callback in self.callbacks:
            callback(message)
```

Here is an example of its usage:

```python
app = Application()

@app.subscribe
def test1(message):
    print("Function 1:", message)

def test2(message):
    print("Function 2:", message)

app.subscribe(test2)

app.emit('Hello World')
```

```
Function 1: Hello World
Function 2: Hello World
```

## Multiple Events

Let's say you want the application to handle different types of events. Now `self.callbacks` is a dictionary of lists, where the key is the event and the list is the same as the last section. There's an additional layered function on top of `subscribe` this time in order to handle passing an argument into the decorator.

```python
from collections import defaultdict
from typing import Callable, Optional
class Application:
    def __init__(self):
        self.callbacks: Dict[str, List[Callable]] = defaultdict(list)
    def on(self, event: str, func: Optional[Callable] = None):
        def subscribe(func: Callable):
            if not callable(func):
                raise ValueError("Argument func must be callable.")
            self.callbacks[event].append(func)
            return func
        if func is None:
            return subscribe
        subscribe(func)
    def emit(self, event, message):
        for callback in self.callbacks[event]:
            callback(message)
```

To show its usage lets first create an instance of `Application`

```python
app = Application()
```

Now let's subscribe a couple functions to `event1`

```python
@app.on('event1')
def test1(message):
    print("Function 1:", message)

def test3(message):
    print("Function 3:", message)

app.on('event1', test3)
```

Now to subscribe a couple events to `event2`

```python
# Subscribed to event 2
@app.on('event2')
def test2(message):
    print("Function 2:", message)

def test4(message):
    print("Function 4:", message)

app.on('event2', test4)
```

We can also subscribe to both events

```python
# Subscribed to both events
@app.on('event1')
@app.on('event2')
def test5(message):
    print("Function 5:", message)
```

```python
app.emit('event1', 'Hello, World!')
```

```
Function 1: Hello, World!
Function 3: Hello, World!
Function 5: Hello, World!
```

```python
app.emit('event2', 'Goodbye, World!')
```

```
Function 2: Goodbye, World!
Function 4: Goodbye, World!
Function 5: Goodbye, World!
```

