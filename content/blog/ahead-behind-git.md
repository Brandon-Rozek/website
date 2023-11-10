---
title: "Figuring out which git repositories are ahead or behind"
date: 2023-11-09T21:05:34-05:00
draft: false
tags: ["Git"]
math: false
medium_enabled: false
---

More often than I care to admit, I would pick up to do work on a device only to realize that I'm working with an older version of the codebase. I could use the `git status` command, but the output is verbose and stale if you haven't `git fetch/pull`'d.

I keep the majority of my git repositories in the folder `~/repo/` on all my devices. Inspired by a recent [blog post by Clayton Errington](https://claytonerrington.com/blog/git-status/), I wanted a way to quickly check within a folder which repositories need updating.  Their blog post has a script written in PowerShell. I decided to write my own bash implementation, and also ignore the bit about modified files since I mostly care about the state of my commits with respect to the `origin` remote.

Before writing a recursive implementation, let's first discuss how to check the ahead/behind status for a single repository.

First things first, you need to make sure that we have all the references from the remote.

```bash
git remote update
```

To print out how many commits the local `main` branch is ahead of the one located on the `origin` remote we can use:

```bash
git rev-list --count origin/main..main
```

Similarly for checking how many commits the local `main` branch is behind we can use:

```bash
git rev-list --count main..origin/main
```

Instead of looking at the `main` branch, maybe we can to check whichever branch we're currently at.

```bash
branch=$(git rev-parse --abbrev-ref HEAD)
```

We can wrap all of this into a nice bash function. We'll additionally check if there is a `.git` in the current folder as none of the git commands will work without it.

```bash
check_remote() {
  if [ -d .git ]; then
    git remote update > /dev/null 2> /dev/null
    branch=$(git rev-parse --abbrev-ref HEAD)
    ahead=$(git rev-list --count origin/$branch..$branch)
    behind=$(git rev-list --count $branch..origin/$branch)
    echo "$ahead commits ahead, $behind commits behind"
  fi
}
```

I currently have 15 repositories in my `~/repo` folder. Now I can `cd` into each of them and run this bash function. Or, I can have `bash` do it for me :)

Let's write a function called `process` that does just that. We'll pass in a folder as an argument stored in `$1`

```bash
process() {
  if [ -d "$1/.git" ]; then
    pushd "$PWD" > /dev/null
    cd "$1"
    echo -n "$1 "
    check_remote
    popd > /dev/null
  fi
}
```

The `pushd` command will keep track of the folder that we're currently in. Then we `cd` into the directory that has `.git` folder. Print the name of the folder so we can associate the ahead/behind counts, and then run the `check_remote` function. Lastly we `popd` back to the folder we started from.

All that's left is to get the list of folders to process:

```bash
find . -type d -print0
```

Feed it into a `while read` loop passing in each folder into the `process` function.

```bash
find . -type d -print0 | while read -d $'\0' folder
do
  process $folder
done
```

All together the script will look like:

```bash
#!/bin/bash

set -o errexit
set -o nounset
set -o pipefail

show_usage() {
  echo "Usage: git-remote-status [-R]"
  exit 1
}

check_remote() {
  if [ -d .git ]; then
    git remote update > /dev/null 2> /dev/null
    branch=$(git rev-parse --abbrev-ref HEAD)
    ahead=$(git rev-list --count origin/$branch..$branch)
    behind=$(git rev-list --count $branch..origin/$branch)
    echo "$ahead commits ahead, $behind commits behind"
  fi
}

if [ "$#" -eq 0 ]; then
  check_remote
  exit 0
fi

if [ "$1" != "-R" ]; then 
  show_usage
  exit 1
fi


process() {
  if [ -d "$1/.git" ]; then
    pushd "$PWD" > /dev/null
    cd "$1"
    echo -n "$1 "
    check_remote
    popd > /dev/null
  fi
}
export -f process

find . -type d -print0 | while read -d $'\0' folder
do
  process $folder
done
```

This gives us two options. If we pass in no flags, then it'll print out the ahead/behind status for the current folder. If we pass in `-R`, then we recursively check all the subfolders as well.

Example Output of `git-remote-status -R`:

```
./project1 0 commits ahead, 3 commits behind
./project2 1 commits ahead, 0 commits behind
./project3 1 commits ahead, 2 commits behind
./project4 0 commits ahead, 0 commits behind
./project5 0 commits ahead, 0 commits behind

```

