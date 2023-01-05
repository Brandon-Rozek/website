---
title: "Python setup.py develop"
date: 2020-02-21T22:42:55-05:00
draft: false
tags: [ "Python" ]
medium_enabled: true
---
**Deprecated in favor of [pip install editable](/blog/pipeditable)**

I've found it to be incredibly helpful to emulate having a library installed on my system rather than depending on my local directory path to pick up my file edits. To do this in a python project where you've defined a `setup.py`, you can specify the command `develop`.

First uninstall whatever version of your `library` you have.
```bash
pip uninstall library
```

Then in your folder with the `setup.py` run the following command
```bash
python setup.py develop
```

This will then create a symlink from your site-packages directory to the directory in which your code lives.

Once you're ready to install it formally,
```bash
pip uninstall library
pip install .
```

Distribute it,
```bash
pip wheel .
```


