---
title: "Python Typing"
date: 2019-10-28T00:12:34-04:00
draft: false
---

There's a typing module built right into Python that you can use on your applications. Sobolevn write a great [blog post](https://sobolevn.me/2019/01/simple-dependent-types-in-python) about it. One thing that threw me off at first is that if you add type annotations and then run python like you normally would, it would act as if the annotations weren't there.

Why use type annotations then?

1. It enhances your internal docs. VS Code and other editors pick this up and show it to the user in their IDE.
2. You can use `mypy` to perform type checking for you.

I go back and forth with type checking in Python, but I do think that forcing yourself to follow type safety makes you a better programmer.