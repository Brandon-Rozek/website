---
title: "Show Applications using the Internet"
date: 2020-05-09T11:30:36-04:00
draft: false
tags: ["Linux", "Networking"]
medium_enabled: true
---

There's a great thread on [ask ubuntu](https://askubuntu.com/questions/104739/which-applications-are-using-internet) on seeing which applications are using the Internet. I'm going to add my own spin on the answers for future reference.

```bash
lsof -i | awk '{print $1}' | uniq | tail -n +2
```

Breaking it down...

- `lsof -i` shows us a lot of information pertaining to processes accessing the Internet.
- `awk '{print $1}'` filters the last output to only shown us the `COMMAND` column.
- `uniq` filters out multiple occurrences of a single application.
- `tail -n +2` removes the first `COMMAND` line.