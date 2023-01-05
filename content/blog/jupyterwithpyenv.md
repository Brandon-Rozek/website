---
title: "Jupyter with Pyenv"
date: 2020-07-21T02:44:06-04:00
draft: false
tags: ["Python"]
medium_enabled: true
---

I enjoy both managing my Python versions with [pyenv](/blog/pyenv/) and the literate programming environment [Jupyter lab](https://jupyter.org/). Luckily we can easily manage Python virtual environments via iPython kernels.

We're going to start off with our base Python interpretor
```bash
pyenv install 3.8.4
pyenv shell 3.8.4
```

Then we're going to install the `ipykernel` package.
```bash
pip install --upgrade pip
pip install ipykernel
```

Next we're going to create a virtual environment where JupyterLab will live.
```bash
pyenv virtualenv jupyter
pyenv activate jupyter
pip install jupyterlab
```

With that, we can now create arbitrary environments and add them as a kernel.
```bash
pyenv deactivate
pyenv virtualenv tensorflow
pyenv activate tensorflow
pip install tensorflow
ipython kernel install --user --name tensorflow
```

