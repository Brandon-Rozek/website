---
title: "Git Pushing to Multiple Remotes"
date: 2022-06-02T21:19:29-04:00
draft: false
tags: ["Git"]
math: false
medium_enabled: true
---

Git's greatest strength is its first-class support for decentralization.
Sadly, GitHub has taken over as the sole location to store code for many
people.

In order to not *put all my eggs into one basket*, I want to utilize multiple
code hosting websites to store my public repositories.
This is not only for the GitHub zombie apocolypse scenario, but local
outages do in fact happen and its nice to have a backup.

Ideally this backup would not come at a cost of convinience. In fact,
we can edit the remotes of our git repository so that a simple
`git push` updates all of our remotes.


The following is an example from my website.
Within your repository, use the command `git config -e` to open an editor with your
repository's git conifguration. Then edit the origin block to be configured
with multiple push-urls.
```ini
[remote "origin"]
        url = git@github.com:Brandon-Rozek/website.git 
        fetch = +refs/heads/*:refs/remotes/origin/*
        pushurl = git@github.com:Brandon-Rozek/website.git
        pushurl = git@git.sr.ht:~brandonrozek/website
```

After this, typing `git push` every pushurl you have configured.
For me, it updates both my [GitHub repository](https://github.com/brandon-rozek/website)
as well as my [SourceHut repository](https://sr.ht/~brandonrozek/website/).

I only recently started using [SourceHut](https://sr.ht/). 
It's designed by [Drew Devault](https://drewdevault.com/)
and others to feature the original usage of git, via email.
This method is still in use by the Linux kernel development team.
I'm excited to try it out and hopefully write some future posts on this concept.
