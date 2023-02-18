---
date: 2022-04-07 20:09:40-04:00
draft: false
math: false
medium_enabled: true
medium_post_id: 7d133254be3f
tags: []
title: 'Permission Denied: Writing to Privileged Locations'
---

Perhaps you've tried something like the following:

```bash
sudo echo "hi" > /etc/test
```

Only to receive back an error

```
bash: /etc/test: Permission denied
```

This is because the `sudo` part only applies to the echo command. Bash which is the process that takes the `"hi"` from the `echo` standard out and writes it to `/etc/test` is still under the unprivileged user.

Instead consider the following:

```bash
echo "hi" | sudo tee /etc/test
```

The command `tee` takes whatever is in standard in, and writes it to the filename specified. Since we applied `sudo ` to the `tee` command, it now has the necessary permissions to write to a privileged location.