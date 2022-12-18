---
title: "Signing Commits"
date: 2020-04-11T19:59:41-04:00
draft: false
tags: ["Git", "GPG"]
---

Git and their various hosting platforms support commit signing as an additional step of verification. There seems to be an active debate on whether it should be used regularly, though I'll describe it on here in case you want to set it up.

You'll need to have a [GPG key already created](/blog/gpgkeygen). 

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

If you want to sign your commits with your main private key, then you can use the main
key's *fingerprint*. In the example above, that's the part that starts with `KDI`.

## (Optional) Creating a signing subkey

Alternatively, we can create a subkey specifically for signing commits.
To do that, first we need to enter the edit mode for that key.

```bash
gpg --edit-key $FINGERPRINT
```
where `$FINGERPRINT` is the same fingerprint above.

You'll see something like the following
```
sec  rsa3072/3E40C8DB05FCCFAD
     created: 2022-12-18  expires: 2023-12-18       usage: SC  
     trust: ultimate      validity: ultimate
ssb  rsa3072/50CC6B37C26F7882
     created: 2022-12-18  expires: 2023-12-18       usage: E   
[ultimate] (1). Brandon Rozek

gpg>
```

From there you type `addkey`, which will then present you with some options
```
Please select what kind of key you want:
   (3) DSA (sign only)
   (4) RSA (sign only)
   (5) Elgamal (encrypt only)
   (6) RSA (encrypt only)
  (14) Existing key from card
Your selection? 
```

As before, I recommend going with the default signing key option.
In this case it's `(3) DSA (sign only)`. 

```
DSA keys may be between 1024 and 3072 bits long.
What keysize do you want? (2048) 
```

As before, either stick with the default or tweak based
on your personal assesment of risk.

```
Please specify how long the key should be valid.
         0 = key does not expire
      <n>  = key expires in n days
      <n>w = key expires in n weeks
      <n>m = key expires in n months
      <n>y = key expires in n years
```

Same advice as before in terms of key expiration.
I generally stick with `1y`. Then, after
confirming the sanity checks you should see the key created.

```
sec  rsa3072/3E40C8DB05FCCFAD
     created: 2022-12-18  expires: 2023-12-18   usage: SC  
     trust: ultimate      validity: ultimate
ssb  rsa3072/50CC6B37C26F7882
     created: 2022-12-18  expires: 2023-12-18   usage: E 
ssb  dsa2048/5C1B6FCA0DABB046
     created: 2022-12-18  expires: 2023-12-18   usage: S   
[ultimate] (1). TestKey
```

The signing key is denoted by the label `usage: S`.
From there we can take its fingerprint, which for
the example above starts with `5C1B` and proceed
with the next step.


## Configuring Git

From here, we need to tell git the key we want to sign with

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

