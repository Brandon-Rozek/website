---
title: "Quick Python: Package Namespacing"
date: 2020-02-03T20:13:38-05:00
draft: false
images: []
---

Package namespacing can help organize modules within a larger project. It can also help show that a package belongs to an organization.

For example, let's say you want to have a module named `companyname.component`. Then you want to have the following project structure.

```
companyname/
  component/
    __init__.py
    ...
setup.py
```

Note that there is no `__init__.py` under `companyname`. 

Then in your `setup.py` denote where to find the packages using a namespace.

```python
from setuptools import setup, find_namespace_packages

setup(name="companyname.component",
     version="0.0.1",
     packages=find_namespace_packages(include=["companyname.*"]))
```

