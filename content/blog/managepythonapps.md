---
title: "Manage Python Applications"
date: 2020-10-11T19:21:10-04:00
draft: false
tags: ["Python"]
---

I've recently discovered an application called [`pipx`](https://pipxproject.github.io/pipx/) which allows one to install and run Python applications in isolated environments. I think of it as a package similar to `apt`, but keeps the packages nice and isolated from one another.

To Install:

```bash
sudo apt install python3-venv pipx
pipx ensurepath
```

By default, it will create the virtualenvs in `~/.local/pipx` and drop executables in `~/.local/bin`.

Install `diceware` using `pipx`:

```bash
pipx install diceware
```

List the virtual environments maintained by `pipx`:

```bash
pipx list
```

Upgrade a package:

```bash
pipx upgrade diceware
```

Add additional dependencies into a package's virtual environment:

```bash
pipx inject package dependency
```

