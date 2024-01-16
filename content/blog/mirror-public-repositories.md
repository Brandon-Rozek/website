---
title: "Mirror Public Repositories"
date: 2023-11-22T12:28:13-05:00
draft: false
tags:
    - Git
    - Archive
math: false
medium_enabled: false
---

Git is designed to be decentralized. However, many people treat it as a centralized solution by depending on services such as GitHub. What we've seen through the [youtube-dl debacle](https://www.zdnet.com/article/riaa-blitz-takes-down-18-github-projects-used-for-downloading-youtube-videos/) is that repositories that we depend on can be taken down.

This isn't to say that GitHub is evil and that we should move to Bitbucket, Gitlab, Source Hut, etc. But this is more of a commentary on what happens when we depend on one service to host our code. Git is designed to be decentralized, we should make use of that fact!

Also, alleged illegal activity is not the only reason repositories are taken down from the Internet. Sometimes, the [developer themselves](https://www.theregister.co.uk/2016/03/23/npm_left_pad_chaos/) decide to take it down.

As individuals, we can maintain mirrors of repositories we care about. That way if it ever gets removed from a particular service, we're not out of luck.

The simplest way to go about this is to `git clone` the repositories you care about, and regularly `pull` through a cron job or systemd timer. Through systemd maybe it'll look like this:

`/etc/systemd/system/refresh-hugo.service`

```ini
[Unit]
Description=Pull latest changes from Hugo

[Service]
Type=oneshot
WorkingDirectory=/home/brandonrozek/repo/hugo
ExecStart=/usr/bin/git pull

[Install]
WantedBy=multi-user.target
```

`/etc/systemd/system/refresh-hugo.timer`

```ini
[Unit]
Description=Pull latest changes from Hugo every week
Requires=refresh-hugo.service

[Timer]
Unit=refresh-hugo.service
OnCalendar=weekly
Persistent=true

[Install]
WantedBy=timers.target
```

Alternatively, you can use a self-hosted git server instance such as [Forgejo](https://forgejo.org/) to set up pull mirrors through the migration tool. As of the time of writing, this is what I currently do with repositories at https://git.brandonrozek.com/github

I do recommend only mirroring/pulling infrequently such as weekly. We don't want to induce unnecessary load on these centralized services.
