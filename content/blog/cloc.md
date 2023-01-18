---
title: "Count Lines of Code (cloc)"
date: 2020-01-25T10:24:16-05:00
draft: false
images: []
medium_enabled: true
---

**C**ount **L**ines **o**f **C**ode is an application included in the standard Ubuntu repositories that counts the lines of code separated by programming language.

It is able to separate out blank lines, comment lines, and actual code lines in the count.  It's quick and easy to use for giving a quick statistic on any given code repository.

To count lines of code in the current directory,

```bash
cloc .
```

An example from my website repository:

```
1019 text files.
894 unique files.                                          
158 files ignored.

github.com/AlDanial/cloc v1.82  T=0.58 s (1501.1 files/s, 213974.9 lines/s)
-----------------------------------------------------------------------
Language             files          blank        comment           code
-----------------------------------------------------------------------
HTML                   581          14457           4041          69754
Markdown               248           6758              0          14620
XML                      9           1201              0           5291
JavaScript               8            478           1282           2623
JSON                    11              0              0           1875
CSS                      7            216             47           1048
TOML                     3             22             17            120
SVG                      1              2              0             20
Bourne Shell             1              0              0              3
-----------------------------------------------------------------------
SUM:                   869          23134           5387          95354
-----------------------------------------------------------------------
```

