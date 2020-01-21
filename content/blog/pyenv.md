---
title: "Managing Python Versions with Pyenv"
date: 2020-01-20T09:55:04-05:00
draft: false
images: []
---

I wrote previously about [managing python virtual environments](https://brandonrozek.com/blog/virtualenv/). Since then, I've discovered a software called [Pyenv](https://github.com/pyenv/pyenv) which allows you to not only manage virtual environments but python versions. As someone who likes to develop python programs in his free time, I found this incredibly useful in keeping all my virtual environments in one place and easily upgrading to a more recent version of python.

To install, follow the steps outlined in the [pyenv-istaller](https://github.com/pyenv/pyenv-installer) repository. As of now, it's a bash script.

## Python Versions

Once it's installed, we need to download a version of python. To see what's available,

```bash
pyenv install --list
```

This will give us a very large list of all the different python versions we can install. Let's say we want to install vanilla Python version 3.8.1. Then all we do is specify that after the install keyword,

```bash
pyenv install 3.8.1
```

Now pyenv has a great concept where you can set certain folders to automatically load a specific python version or virtual environment. To set the current directory to use python 3.8.1 by default, run the following command:

```bash
pyenv local 3.8.1
```

This will then create a file called `.python-version` which contains the text `3.8.1`. To set this globally, just replace `local` with `global`,

```bash
pyenv global 3.8.1
```
Finally, if you only want to specify a python version for the current shell.
```bash
pyenv shell 3.8.1
```

## Python Virtual Environments

To create a virtual environment, run the following

```bash
pyenv virtualenv name
```

This will create a virtual environment called `name` that is bound to the version of Python you have enabled at the current moment. 

Once it's created you can activate it with the following,

```bash
pyenv activate name
```

You can also use the `local` and `global` pyenv commands to set the current directory or default to be the virtual environment. To do that, all we need to do is replace the python version from above with the environment name

```bash
pyenv local name
```

With this, you now have a python virtual environment to play with!

## Other useful commands

Which version or virtual environment am I using?

```bash
pyenv version
```

Which versions or virtual environments are available to me?

```bash
pyenv versions
```

Which virtual environment or version contains a command I'm looking for? (e.g spyder)

```bash
pyenv whence executable
```

