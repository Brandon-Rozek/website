---
title: "Do-While Loop in Other Languages"
date: 2021-08-27T21:50:02-04:00
draft: false
tags: []
math: false
medium_enabled: true
---

Some languages like C, C++, and Java have a concept of a Do-While loop which normally look like the following:

```
do {
    statements;
} while(condition);
```

This would ensure that your group of statements at least run once and then continue while the condition is still met. If you're used to that pattern, then it can be annoying when you switch to another language like Python and find that it doesn't exist. To replicate this behavior, its as simple as adding an extra variable.

```python
first_run = True
while condition or first_run:
    first_run = False
    statements
```


