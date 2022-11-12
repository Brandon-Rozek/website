---
title: "GPG Keygen"
date: 2020-04-11T19:35:05-04:00
draft: false
tags: ["GPG"]
---

GPG keys have a variety of different uses from sending encrypted emails to verifying git commits. Here I'll show how easy it is to create a public/private key-pair. Assuming you have the `gpg` client installed.

Type the following command

```bash
gpg --full-gen-key
```

This will then show

```
gpg (GnuPG) 2.2.12; Copyright (C) 2018 Free Software Foundation, Inc.
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.

Please select what kind of key you want:
   (1) RSA and RSA (default)
   (2) DSA and Elgamal
   (3) DSA (sign only)
   (4) RSA (sign only)
Your selection? 1
```

I selected the default option.

```
RSA keys may be between 1024 and 4096 bits long.
What keysize do you want? (3072) 4096
Requested keysize is 4096 bits
```

I went for the highest available option.

```
Please specify how long the key should be valid.
         0 = key does not expire
      <n>  = key expires in n days
      <n>w = key expires in n weeks
      <n>m = key expires in n months
      <n>y = key expires in n years
Key is valid for? (0) 1y
```

It's highly recommended that you set an expiration date. I usually set it for around 1-3 years.

```
Key expires at Mon 11 Apr 2021 06:42:01 PM EDT
Is this correct? (y/N) y
```

Quick sanity check.

```
GnuPG needs to construct a user ID to identify your key.

Real name: Brandon Rozek
Email address:
Comment: Git

```

All the fields are optional.  Fill them in as you wish.

```
You selected this USER-ID:
    "Brandon Rozek (Git)"
Change (N)ame, (C)omment, (E)mail or (O)kay/(Q)uit? O
```

More sanity checks.

```
We need to generate a lot of random bytes. It is a good idea to perform
some other action (type on the keyboard, move the mouse, utilize the
disks) during the prime generation; this gives the random number
generator a better chance to gain enough entropy.
```

Do as it says, start going crazy.

```
gpg: key IFMWDHXYSKTICHSE marked as ultimately trusted
public and secret key created and signed.

pub   rsa4096 2020-04-11 [SC] [expires: 2021-04-11]
      FDMGHVYEIWPDKVT83ICUZOEKSLFIVYQALKZMNTYR
uid                      Brandon Rozek (Git)
sub   rsa4096 2020-04-11 [E] [expires: 2021-04-11]
```

Congratulations, you now have a GPG key set.