---
title: "Git Credential Store"
date: 2020-05-25T22:30:49-04:00
draft: false
tags: ["Git"]
---

Normally it is recommended to setup a SSH key with your Git hosting tool with choice. Though if that is not practical, another way you can avoid having to put in your git username and password every time you push your code is to make use of Git's credential store.

To enable it globally across your projects

```bash
git config --global credential.helper store
```

Then you can edit the file `~/.git-credentials` with the following format

```
https://username1:password1@site1.com
https://username2:password2@site2.com
```

It is recommended to set your `.git-credentials` file with the same permissions you would see in a SSH private key file. Read and write permissions for the user only.

```bash
chmod 600 ~/.git-credentials
```

