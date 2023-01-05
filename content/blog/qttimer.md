---
title: "Qt Timers"
date: 2020-03-19T17:30:04-04:00
draft: false
tags: ["C++"]
medium_enabled: true
---

Qt has two great timers, one that repeats an action after a certain interval, and one that is meant for one-off operations. They call these `QTimer` and `QTimer::singleShot` respectively. This post is going to assume that we're working with a class named `Test` that inherits `QObject`.

Let us first look at the one that repeats. This code needs to be inside a class that inherits `QObject`.
```c++
void Test::callbackRepeat(void) {
    // Code that executes when the timer times out
}

// ......
int interval = 1000; // Units: milliseconds
QTimer* timer = new QTimer(this);
timer->start(interval);
connect(timer, &QTimer::timeout, this, &Test::callbackRepeat);
```

Now for the one-off...

```c++
void Test::callback(void) {
	// Code that executes when the timer times out
}

// ......
int timeout = 1000; // Units: milliseconds
QTimer::singleShot(timeout, this, &Test::callback)
```

