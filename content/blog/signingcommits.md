---
title: "Signing Commits"
date: 2020-04-11T19:59:41-04:00
draft: false
tags: ["Git", "GPG"]
---

Git and their various hosting platforms support commit signing as an additional step of verification. There seems to be an active debate on whether it should be used regularly, though I'll describe it on here in case you want to set it up.

You'll need to have a [GPG key already created](https://brandonrozek.com/blog/gpgkeygen). 

First locate the key you want to sign with

```bash
gpg --list-secret-keys --keyid-format SHORT
```

This will output something like
```
/home/user/.gnupg/pubring.kbx
------------------------------
sec   rsa4096/8294756F 2020-04-11 [SC] [expires: 2021-04-11]
      KDIAUBEUX837DIU79YHDKAPOEMNCD7123FDAPOI
uid         [ultimate] Brandon Rozek (Git)
ssb   rsa4096/9582109R 2020-04-11 [E] [expires: 2021-04-11]
```

Copy the string starting with "KDI..". This will be your *fingerprint*.

Now tell git the key you want to sign with

```bash
git config --global user.signingkey $FINGERPRINT
```

To sign a commit, add a `-S` flag

```bash
git commit -S -m "Initial Commit"
```

To always sign your commits

```bash
git config --global commit.gpgsign true
```

Remember to add your public key to Github, Gitlab, etc. You can get it by

```bash
gpg --armor --export $FINGERPRINT
```

