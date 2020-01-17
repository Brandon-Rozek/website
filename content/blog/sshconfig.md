---
title: "SSH Config"
date: 2019-09-27T22:46:39-04:00
draft: false
---

Have you ever gone through the hassle of having multiple public/private keys for accessing your remote servers? Before recently, I used to specify the identity file in all my transactions `ssh -I ~/.ssh/private_key user@host` but no longer! I discovered you can add the following to your `~/.ssh/config` to specify which key you want to use!

```
Host somename 
    Hostname someaddress
    user usernameonserver
    IdentityFile ~/.ssh/private_key
```

Of course you can add multiple of these entries in that file so that you can `ssh` without having to worry about explicitly using keys.
