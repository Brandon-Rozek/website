---
title: "Bat: The user friendly cat"
date: 2020-02-01T06:26:18-05:00
draft: false
tags: [ "linux" ]
---

`bat` is a more human pleasing replacement of `cat` with the following features:

- syntax highlighting support
- git integration
- automatic paging

To test it out I wrote a file called `test.py`

```python
from collections import Counter

items = [1,3,1,6,3]
c = Counter(items)

print(c[1])
```

And here's a screenshot of my terminal session when I called `bat`

![image-20200201063050726](/files/images/20200201063050726.png)
