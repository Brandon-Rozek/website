---
title: "Filesystem as a persistent key-value store in Python"
date: 2025-04-27T13:39:49-04:00
draft: false
tags:
  - key-value database
  - file system
  - Python
math: false
medium_enabled: false
---

The first level within the [five levels of configuration languages](https://beza1e1.tuxen.de/config_levels.html) is a string in a file. The example that Andreas gives in his blog post is enabling/disabling energy aware scheduling in the kernel.

```bash
# Read the current value
cat /proc/sys/kernel/sched_energy_aware
```

This approach does not require using any custom serializers or deserializers. Instead, the user or program only needs to navigate and read/write the filesystem.[^1]

[^1]: You likely want to make sure that your program is sufficiently isolated. Either by running it within it's own container or setting up custom permissions on the files.

However, having to write filesystem code is tedious. What we want is a dictionary that we can write and read from that handles all of the filesystem procedures for us.

In this post, we'll go over how to achieve this in Python. By the end we'll be able to do the following:

```bash
# Create key-value store
mkdir /tmp/kvs
# Add value "Brandon" to key "name"
echo "Brandon" | tee /tmp/kvs/name
```

```python
# Set /tmp/kvs as the root of our key-value store
kvs = FSDict("/tmp/kvs")
# Read the key 'name'
print("Name:", kvs['name'])
# Name: Brandon
```

## Creating the library

To emulate reading and writing from a dictionary, we will create a custom class and implement the `__setitem__` and `__getitem__` methods.

```python
class FSDict:
  def __init__(self, base_directory: Optional[str] = None):
    self.base_directory: Optional[str] = None
    if base_directory is not None:
      self.set_base_directory(base_directory)
  
  def set_base_directory(self, base_directory: str):
    assert isinstance(base_directory, str)
    if os.path.isfile(base_directory):
      raise Exception("base_directory is an existing file not a folder.")
    
    self.base_directory = base_directory
    if not os.path.exists(base_directory):
      os.makedirs(base_directory)
  
  # ...
```

From here, we can declare a folder as the root of our key-value store and if it does not exist then the code will create it for us.

```python
kvs = FSDict("/tmp/kvs")
```

When we write `kvs['name']`, we want it to read from the file or folder `/tmp/kvs/name`. Our next method then will create the path.

```python
def get_path(self, key: str) -> str:
  assert self.base_directory is not None
  if not isinstance(key, str):
    raise ValueError("key must be of type str")
  return os.path.join(self.base_directory, key)
```

Just like in our initial kernel example, we want a way to have nested folders. Therefore, in this API when we read and write from the KVS, if the value is a `str` then we're writing it's contents to a file, otherwise if it is a `FSDict` then we'll create the folder if it does not already exist.

To write to our key-value store:

```python
def __setitem__(self, key: str, value: Union[str, "FSDict"]):
  assert isinstance(value, (str, FSDict)), "Value must either be of type str or FSDict"
  path = self.get_path(key)
  
  # If we're writing a FSDict, then create
  # a folder if it doesn't already exist.
  if isinstance(value, FSDict):
    value.set_base_directory(path)
    return None

  # Otherwise, assume we're writing a
  # string to a file
  with open(path, "w") as f:
    f.write(value)
```

To read from our key-value store:

```python
def __getitem__(self, key: str) -> Union[str, "FSDict"]:
  path = self.get_path(key)
  
  if not os.path.exists(path):
    raise KeyError(key)
  
  # Return a FSDict if it's a folder
  if os.path.isdir(path):
    return FSDict(path)

  # Otherwise, assume we're reading a file
  with open(path, "r") as f:
    return f.read()
```

With that, we have the minimum viable product for reading and writing to our dictionary-like class!

```python
kvs = FSDict("/tmp/kvs")
kvs['name'] = 'Brandon'
print(kvs['name'])
# Prints 'Brandon'
```

The base dictionary class has other methods that make our lives easier. Let's implement a few more.

```python
def __delitem__(self, key: str):
  path = self.get_path(key)

  if not os.path.exists(path):
    raise KeyError(key)

  # If the key is a folder, recursively
  # remove all contents of that folder
  if os.path.isdir(path):
    shutil.rmtree(path)
    return None

  # Otherwise, remove the file
  os.remove(path)
    
def __contains__(self, key: str) -> bool:
  path = self.get_path(key)
  return os.path.exists(path)
    
def keys(self) -> List[str]:
  assert self.base_directory is not None
  return os.listdir(self.base_directory)

def __repr__(self) -> str:
  return f"FSDict(base_directory={self.base_directory})"
```

Extending our last example, this gives us:

```python
# Show all keys
print(kvs.keys())
# Result: ['name']

# Check if a key is in the key-value store
print('name' in kvs)
# Result: True

# Delete a key-value by it's key
del kvs['name']

# Check if it still exists in our key-value store
print('name' in kvs)
# Result: False
```

## Conclusion

The class `FSDict` provides a simple way in Python to use the filesystem as a persistent key-value store. Unlike storing everything in a single file or database, we do not need special serializers or deserializers to access to data. Outside the program we can use `echo` and `cat` in our terminals to interact with the key-value store.

The full code is as follows:

```python
from typing import List, Optional, Union
import os
import shutil

class FSDict:
    def __init__(self, base_directory: Optional[str] = None):
        self.base_directory: Optional[str] = None
        if base_directory is not None:
            self.set_base_directory(base_directory)
    
    def set_base_directory(self, base_directory: str):
        assert isinstance(base_directory, str)
        if os.path.isfile(base_directory):
            raise Exception("base_directory is an existing file not a folder.")
        
        self.base_directory = base_directory
        if not os.path.exists(base_directory):
            os.makedirs(base_directory)
    
    def get_path(self, key: str) -> str:
        assert self.base_directory is not None
        if not isinstance(key, str):
            raise ValueError("Key must be of type str")
        return os.path.join(self.base_directory, key)
    
    def __setitem__(self, key: str, value: Union[str, "FSDict"]):
        assert isinstance(value, (str, FSDict)), "Value must either be of type str of FSDict"
        path = self.get_path(key)

        if isinstance(value, FSDict):
            value.set_base_directory(path)
            return None

        # Assuming value is a str
        with open(path, "w") as f:
            f.write(value)

    def __getitem__(self, key: str) -> Union[str, "FSDict"]:
        path = self.get_path(key)

        if not os.path.exists(path):
            raise KeyError(key)

        if os.path.isdir(path):
            return FSDict(path)

        # Assume it's a file
        with open(path, "r") as f:
            return f.read()

    def __delitem__(self, key: str):
        path = self.get_path(key)

        if not os.path.exists(path):
            raise KeyError(key)

        if os.path.isdir(path):
            shutil.rmtree(path)
            return None

        # Assume it's a file
        os.remove(path)
    
    def __contains__(self, key: str) -> bool:
        path = self.get_path(key)
        return os.path.exists(path)
    
    def keys(self) -> List[str]:
        assert self.base_directory is not None
        return os.listdir(self.base_directory)

    def __repr__(self) -> str:
        return f"FSDict(base_directory={self.base_directory})"

```

