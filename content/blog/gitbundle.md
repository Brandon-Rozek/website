---
title: "Git Bundle"
date: 2020-03-20T16:22:01-04:00
draft: false
tags: ["Git"]
medium_enabled: true
---

If you have a large software repository, sometimes you only want to share part of it with a group. You can accomplish this by using `git bundle`

## Creating the Bundle

To bundle all the commits from the development branch to the current head,

```bash
git bundle create repo.bundle development..HEAD feature_branch
```

This will place these commits into a branch called `feature_branch` in `repo.bundle`.

## Fetching from bundle

On the other side, we need to make sure that we have all the commits up to the `development` branch synchronized. Then we can fetch the commits from the bundle:

```bash
git fetch /path/to/repo.bundle feature_branch:feature_branch
```

The left side of the colon is what you want to grab from the bundle, the right side is the branch to put the commits to.

```bash
git checkout feature_branch
```

