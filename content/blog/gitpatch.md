---
title: "Sharing Patches in Git"
date: 2020-03-20T16:22:57-04:00
draft: false
tags: ["Git"]
medium_enabled: true
---

The Linux kernel community make use of patches in git to share code changes with one another. Patches are only nicely formatted differences between your current codebase and what you compare it to. If you want to share a subsetted git tree, then [git bundle](/blog/gitbundle) would be the way to go. 

## Creating the patch

If you want to create a patch based off the difference between your current branch and master, run the following:

```bash
git format-patch master --stdout > feature_branch.patch
```

You can then email the patch to the team.

## Applying the patch

To apply go into a new branch and apply the patch file.

```bash
git checkout -b feature_branch
git apply /path/to/feature_branch.patch
```