---
title: "Python Argument Parser"
date: 2022-05-16T17:07:06-04:00
draft: false
tags: ["Python"]
math: false
---

*For a much better description of argument parsing in Python, please visit https://docs.python.org/3/library/argparse.html.*

I'm creating this post because even though it's not too complicated, I keep forgetting how to do argument parsing in Python. I also tricked myself into thinking each time that I already wrote a blog post on this. Let's correct this once and for all and include a quick example!

```python
import argparse
parser = argparse.ArgumentParser(description="Description to show in help")
parser.add_argument("pos_arg1", type=str, help="Required positional argument")
parser.add_argument("--flag1", type=str, help="Optional flag argument")
parser.add_argument("--flag2", type=int, required=True, help="Required flag argument")
args = vars(parser.parse_args())
```

Now if you call the program with no arguments you'll get the following message:

```
usage: testarg.py [-h] [--flag1 FLAG1] --flag2 FLAG2 pos_arg1
testarg.py: error: the following arguments are required: pos_arg1, --flag2
```

This comes with a built in `-h` as well!

```
usage: testarg.py [-h] [--flag1 FLAG1] --flag2 FLAG2 pos_arg1

Description to show in help

positional arguments:
  pos_arg1       Required positional argument

optional arguments:
  -h, --help            show this help message and exit
  --flag1 FLAG1         Optional flag argument
  --flag2 FLAG2         Required flag argument
```

Within the code you can parse the argument names by accessing the `args` dictionary.

```python
pos_arg1 = args['pos_arg1']
flag1 = args['flag1']
flag2 = args['flag2']
```



