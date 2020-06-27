---
title: "GPG Agent as SSH Agent"
date: 2020-06-14T22:33:01-04:00
draft: false
tags: []
---

GPG Agent has the ability to act as a SSH Agent. This allows the use of Authentication keys on Smartcards to be used with SSH as well.

First we need to enable SSH support in GPG Agent,

```bash
echo "enable-ssh-support" >> ~/.gnupg/gpg-agent.conf
```

Then we need to specify an environmental variable for the SSH Daemon to use GPG Agent

```bash
echo "export SSH_AUTH_SOCK=$(gpgconf --list-dirs agent-ssh-socket)" >> ~/.bashrc
```

If you want it to be active immediately, then source the bashrc,

```bash
source ~/.bashrc
```

If you have a smartcard plugged in, then you should be able to see it via the GPG agent

```bash
ssh-add -l
```

