---
title: "Offline Pip Packages"
date: 2020-01-20T23:11:05-05:00
draft: false
tags: [ "python", "archive" ]
---

There are a few reasons I can think of to have offline pip packages:

- A package isn't able to compile on a friend's computer since they don't have the million linear algebra libraries that `numpy` /`scipy` require.
- You want to archive everything to run a piece of software
- You want to control the packages available to a closed network

Regardless, to my surprise, setting up a repository of python wheels doesn't take many steps. 

## Setup

First I would recommend that you setup a virtual environment. Either through [pyenv](https://brandonrozek.com/blog/pyenv/) or [python-virtualenv](https://brandonrozek.com/blog/virtualenv/).

Then, install whatever packages you would like. Let us use tensorflow as an example:

```bash
pip install tensorflow
```

We're going to need the packages `pip-chill` and `pip-tools` for the next couple steps

```bash
pip install pip-chill pip-tools
```

After you install all the packages you want to be available, freeze the requirements that aren't dependencies to a text file

```bash
pip-chill --no-version > requirements.in
```

We will then use `pip-compile` in `pip-tools` to resolve our dependencies and make our packages as fresh as possible.

```bash
pip-compile requirements.in
```

To sync the current virtual environment with the `requirements.txt` file that gets produced

```bash
pip-sync
```

Now we have a fully working and resolved environment.

From here, we need to install the wheel package to make the binary wheels.

```bash
pip install wheel
```

Then to create the wheels,

```bash
pip wheel --wheel-dir=wheels -r requirements.txt
```

With this you have a whole repository of wheels under the wheels folder!

## Client Side

Now you can get [all fancy with your deployment](https://realpython.com/offline-python-deployments-with-docker/#deploy), though I just assumed that the files were mounted in some shared folder.

The client can install all the wheels

```bash
pip install /path/to/wheels/*
```

Or they can just install the packages they want

```bash
pip install --no-index -f /path/to/wheels/wheels package_name
```

