---
title: "Python Virtual Environments"
date: 2019-05-21T23:04:54-04:00
draft: false
tags: [ "Python" ]
---

Dependency management is hard.  Luckily with Python there is a program called `virtualenv` that can help isolate different projects and manage dependencies.

## Commands

To create a new python 3.7 environment type in the following:

```bash
virtualenv --python=python3.7 environment_name
```

Of course you can replace the python version with whichever version you like. Now to go into the environment do the following:

```bash
source environment_name/bin/activate
```

This now sets up your python interpretor and other utilities to use the installation in the `environment_name` folder. You can now install python packages using `pip` and have it only reside in this environment.

To save all currently installed packages into `requirements.txt`:

```bash
pip freeze > requirements.txt
```

You can then install those packages in a different virtualenv session with:

```bash
pip install -r requirements.txt
```

You can leave the virtualenv session with:

```bash
deactivate
```

