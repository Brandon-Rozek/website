---
title: "Reverse One-Hot Encode"
date: 2020-10-11T21:58:47-04:00
draft: false
tags: ["Python"]
---

Let's say that you have a dataset that is one hot encoded like the following observation:

```python
import numpy as np
obs = np.array([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0])
```

The easiest way to reverse one-hot encode the structure, is to take the `argmax` of the observation.

```python
reverse_encoding = np.argmax(obs)
# 13
```

