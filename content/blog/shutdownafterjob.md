---
title: "Shutdown After Job"
date: 2019-08-30T20:43:56-04:00
draft: false
---

I'm back to running longer jobs as part of my research. If I run a task overnight, I want to conserve energy and not keep it running after I finish. I suppose this would also apply to cloud billing, you want it to do the job and then stop.

This technique will require you to have sudo privileges on the machine.

1. Change user to root.

```bash
sudo su
```

2. Run job as regular user, write output to file, and then poweroff.

```bash
su -u user task > output.txt && chown user:user output.txt && poweroff 
```

