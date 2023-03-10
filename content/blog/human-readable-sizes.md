---
date: 2021-03-15 23:11:35
draft: false
math: true
medium_enabled: true
medium_post_id: 2a32b08bd2c1
tags: []
title: Human Readable Sizes
---

When playing with large and small values, it is useful to convert them to a different unit in scientific notation. Let's look at bytes.

```python
size_categories = ["B", "KB", "MB", "GB", "TB"]
```

You can figure out how to best represent it by seeing how many of the base (in this case 1000) fits into the value.
$$
category = \lfloor \frac{\log{(size_{bytes})}}{\log{(base)}} \rfloor
$$
You'll want to make sure that you don't overflow in the number of categories you have

```python
category_num = min(category_num, len(size_categories))
```

You can then get its category representation by
$$
size = \frac{size_{bytes}}{(2^{category})}
$$
We can wrap this all up info a nice python function

```python
def humanReadableBytes(num_bytes: int) -> str:
    base = 1000
    
    # Zero Case
    if num_bytes == 0:
        return "0"
    
    size_categories = ["B", "KB", "MB", "GB", "TB"]
    category_num = int(math.log(num_bytes) / math.log(base))
    
    # Make sure it doesn't overflow
    category_num = min(category_num, len(size_categories) - 1)
    
    return "{:.2f} ".format(num_bytes / (base ** category_num)) + \
			size_categories[category_num]
```