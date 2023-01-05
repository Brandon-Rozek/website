---
title: "Tox"
date: 2020-02-21T22:34:19-05:00
draft: false
tags: [ "Python", "Testing" ]
medium_enabled: true
---

[Tox](https://tox.readthedocs.io/en/latest/) is a great project where you can automate your testing using virtual environments.

First install tox
```bash
pip install tox
```

I like to write my tests in Python's native [`unittest`](https://docs.python.org/3/library/unittest.html) format. Tests should be stored in a `tests` directory.

I then combine it with the `coverage` library to tell me how much of my code that my test cases cover. To quickly insert my personal opinion, I never aim for 100% test coverage since there's typically overhead in maintaining that. 

This all gets described in a `tox.ini` file. This file should live in the same directory as your `setup.py`

```ini
[tox]
envlist =
    py38

[testenv]
deps = coverage
commands =
    coverage run --source=tests,library -m unittest discover tests
    coverage report -m
```

