---
title: "Iteratively Read CSV"
date: 2020-04-11T21:34:33-04:00
draft: false
tags: ["python"]
---

If you want to analyze a CSV dataset that is larger than the space available in RAM, then you can iteratively process each observation and store/calculate only what you need. There is a way to do this in standard Python as well as the popular library Pandas.

## Standard Library

 ```python
import csv
with open('/path/to/data.csv', newline='') as csvfile:
    reader = csv.reader(csvfile, delimeter=',')
    for row in reader:
        for column in row:
            do_something()
 ```

## Pandas

Pandas is slightly different in where you specify a `chunksize` which is the number of rows per chunk and you get a pandas dataframe with that many rows

```python
import pandas as pd
chunksize = 100
for chunk in pd.read_csv('/path/to/data.csv', chunksize=chunksize):
    do_something(chunk)
```

