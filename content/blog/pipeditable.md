---
title: "Pip Editable"
date: 2020-04-11T20:38:33-04:00
draft: false
tags: ["Python"]
medium_enabled: true
---

I've found it to be incredibly helpful to emulate having a library installed on my system rather than depending on my local directory path to pick up my file edits. To do this in a python project, we need to add the `--editable` flag to a pip install.

First uninstall whatever version of your `library` you have.
```bash
pip uninstall library
```

Then in your folder with the `setup.py` run the following command
```bash
pip install --editable .
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