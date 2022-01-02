---
title: "Python Packaging: Optional Dependencies"
date: 2020-05-01T00:43:07-04:00
draft: false
tags: ["Python"]
---

It is possible to make different package group of optional dependencies for a Python package. This is useful if you want to include an extra set of dependencies for developers/maintainers of the package. We can also define a plugin-based package similarly to how [OpenAI Gym uses it](https://github.com/openai/gym/blob/67212547ac29296839434324a0d5996e48fae840/setup.py) to denote different categories of environments you can setup.

```python
from setuptools import setup, find_packages

extras = {
  'typing': ['mypy~=0.740', 'mypy-extensions~=0.4.0', 'pylint~=2.4.4'],
  'testingdocs': ['tox~=3.14.6', 'Sphinx~=3.0.1'],
}

# Meta dependency groups.
extras['all'] = [item for group in extras.values() for item in group]

setup(name='example',
      version='0.0.1',
      packages=find_packages(),
      install_requires=['Flask~=1.1.1'],
      extras_require=extras,
)
```

