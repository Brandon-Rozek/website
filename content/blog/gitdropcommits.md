---
title: "How to Drop Commits in Git"
date: 2020-05-26T00:48:37-04:00
draft: false
tags: ["Git"]
medium_enabled: true
---

Even though it is not recommended to rewrite history in Git, it can be useful to drop certain commits from a pull request. The easiest way I've found to achieve this is with `git rebase`. To look back at the last 5 commits

```bash
git rebase -i HEAD~5
```

This will produce a view like the following:

```
pick bda8e1d Follow better coding standards
pick ed62936 Bad Commit
pick 5b89e82 Refactoring to make more sense
pick 2941129 Delete Everything
pick 04d6558 New Feature
```

You can then change the commits you want to remove from `pick` to `drop`.

```
pick bda8e1d Follow better coding standards
drop ed62936 Bad Commit
pick 5b89e82 Refactoring to make more sense
drop 2941129 Delete Everything
pick 04d6558 New Feature
```

Once you exit out, the two commits will be dropped.

Instead of analyzing the last 5 commits, you can also analyze the commits made after branching out. Let's say we're on a feature branch based on the `development` branch.

```bash
git rebase -i development
```

From there you would get the same `pick/drop` screen as before.