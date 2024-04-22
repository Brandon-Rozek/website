---
title: "Tracking Software Releases via RSS"
date: 2024-04-21T23:18:47-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

I have [automatic updates](https://docs.fedoraproject.org/en-US/quick-docs/autoupdates/) set up on most of my machines. It's great for the majority of software packages that don't require manual intervention.

On the other hand some of my self-hosted services (and even my OPNsense router), require me to be slightly more diligent. That is to say, I have enough scars from letting my databases auto-update. I now make sure to check the migration notes.

However promptness-wise, I was not great.  Usually a few months would go by before the thought of software updates came to mind. From there, I would manually check the current software version of each software service I was currently running.

Nowadays, that is no more! I am a completely changed person. Thanks to the power of RSS.

GitHub automatically generates RSS feeds for the releases page (as well as tags) for all of their hosted repositories. Plop that into your favorite RSS reader, and you can get notified whenever a new version is released!

Ex: https://github.com/nextcloud/server/releases



