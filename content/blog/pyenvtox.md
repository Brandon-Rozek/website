---
title: "Testing your Python Application on Multiple Versions with Pyenv and Tox"
date: 2020-02-21T19:06:40-05:00
draft: false 
tags: [ "Python", "Testing" ]
medium_enabled: true
---

Pyenv is great for managing multiple python installations and tox is great for creating virtual environments for testing. What if we can combine the two? For more detailed information visit [Frank-Mich's Blog](https://blog.frank-mich.com/recipe-testing-multiple-python-versions-with-pyenv-and-tox/).

First make sure [pyenv is installed](https://github.com/pyenv/pyenv-installer). In the directory with your `setup.py` tell `pyenv` which python versions you want to consider.
```bash
pyenv local 3.6.0 3.7.0 3.8.0
```

Frank warns heavily not to specify multiple python versions with the same `major.minor` numbering. For example, `3.6.0` and `3.6.10` should not be included together.

Then install the `tox` package.
```bash
pip install tox
```

I made the mistake of making a virtual environment and then installing tox. That gets rid of the python version information we specified before.

Now specify a `tox.ini` with a structure similar to below..
```ini
[tox]
envlist = 
    py36
    py37
    py38

[testenv]
commands = 
    python3 -m unittest discover tests
```

