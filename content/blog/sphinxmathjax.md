---
title: "Sphinx & MathJax"
date: 2020-03-20T18:59:40-04:00
draft: false
tags: ["Documentation", "python", "LaTex"]
---

To include mathematical notation in Python docs generated by Sphinx, it should look like the following:

```python
class Line:
    r"""
    Holds the equation for a line.
    
    :math:`y = mx + \frac{b}{1}`
    
    In this equation, :math:`m` is the slope and :math:`b` is the y-intercept.
    """
    pass
```

The content after `:math:` and inside the backticks is treated as inline math. The `r` in front of the triple quotes is used to make it a raw string and so that LaTex commands such as `\frac{}{}` operate as intended. There also cannot be a space between `:math:` and the backtick. 

The Sphinx configuration needs to have the `mathjax` extension loaded as well.

```python
extensions = [
    # ....
    "sphinx.ext.mathjax",
    # ....
]
```
