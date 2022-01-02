---
title: "Quick Python: List Files Recursively"
date: 2020-02-09T17:31:44-05:00
draft: false
tags: [ "Python" ]
---

In order to add website files into a Flask application using setuptools, I needed to recurse down several directories and grab HTML and CSS files.

This Python tip will show you how to get a list of files recursively. 

First in order to solve this problem, we're going to recursively get a list of directories.

```python
from glob import glob
directories = glob('/path/to/directory/**/', recursive=True)
```

Now we will go in each directory and grab the files, 

```python
data_files = []
for directory in directories:
    data_files += list(filter(lambda x: x + '/'  not in directories, glob(directory + '*')))
```

For setuptools, you would want the `data_files` variable to be a list of tuples with module names and the files associated with them.

Complete script:

```python
data_files = []
directories = glob('path/to/files/**/', recursive=True)
for directory in directories:
    files = list(filter(lambda x: x + '/' not in directories, glob(directory + "*")))
    data_files.append((directory, files))
```
For setuptools don't forget to `include_package_data`!
