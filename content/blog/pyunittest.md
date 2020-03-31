---
title: "Quick Python: Unit Testing"
date: 2020-03-31T07:27:47-04:00
draft: false
tags: ["python"]
---

Python has a great built-in [unit test](https://docs.python.org/3.7/library/unittest.html) framework. This post will give a skeleton for how to format the files in your `tests` directory.

Example `tests/test_basic.py`

```python
import unittest

class Tester(unittest.TestCase):
    def setUp(self):
        """To Run Before Every Test Case"""
        pass

    def tearDown(self):
        """To Run After Every Test Case"""
        pass

    def test_something(self):
        """A Test Case"""
        self.assertEqual(True, True)

if __name__ == '__main__':
    unittest.main()
```

To auto-discover and run your tests

```bash
python -m unittest discover
```



