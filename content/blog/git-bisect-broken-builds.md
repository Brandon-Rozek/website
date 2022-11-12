---
title: "Which commit broke the build? Using Git Bisect"
date: 2022-05-03T01:15:55-04:00
draft: false
tags: ["Git"]
math: false
---

Lets imagine a scenario where in the latest merge a test
starts failing. Lets say these tests are saved
in `test.sh`. Instead of having to test each individual
commit in the merge, to see where the test fails, luckily
`git bisect` narrows it down in a more efficient way!

To use:
```bash
git bisect start [good] [bad]
git bisect run test.sh
```
Where `[good]` and `[bad]` are replaced with their respective
commit hashes.

Under the hood, Git will run a binary search between the good
and bad nodes in the commit tree.

As a reminder, don't forget to make `test.sh` an executable.
Starting in Git 2.36 it will provide a warning, but earlier
versions will perform the search anyways even with it all
failing.


Read more: https://git-scm.com/docs/git-bisect