---
title: "Renewing my GPG Keys"
date: 2023-12-28T11:46:33-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

Recently I let my GPG keys expire. I noticed this when I was working on a project, and when I went to [automatically sign my commits](/blog/signingcommits/) -- git threw an error at me. Since I was working at the time, I did the not-so-great practice of disabling the signing feature. 

Having keys automatically expire is annoying. Though, it does give me a chance to reflect if these keys are still useful to me.  Currently I use GPG keys for: 

- Code signing
- Receiving encrypted messages
- [Decentralized Identity](/blog/decentralized-identity-pgp-keyoxide/)

So to me, having a GPG key is still worth it. Now to go about renewing my keys. This post will show how I go about the renewing process itself and what services I update. Mostly for me in the future.

## Renewing my GPG key

First, find your key

```bash
gpg --list-keys
```

```
/home/brandon/.gnupg/pubring.kbx
------------------------------
pub   ed25519 2022-12-14 [SC] [expires: 2023-12-14]
      5F37830BFA46FF7881F47AC78DF79C3DC5FC658A
uid           [ultimate] Brandon Rozek <brozek@brandonrozek.com>
uid           [ultimate] Brandon Rozek <hello@brandonrozek.com>
sub   cv25519 2022-12-14 [E] [expires: 2023-12-14]
sub   dsa2048 2022-12-17 [S] [expires: 2023-12-14]
```

The fingerprint is the line below `pub` and for me starts with `5F37`. Let's store that in a variable for easy reference later.

```bash
export FPR=5F37830BFA46FF7881F47AC78DF79C3DC5FC658A
```

If we want to extend the expiration date to a year from today, we can use the following command:

```bash
gpg --quick-set-expire $FPR 1y
```

Alternatively, you can specify an exact date with the ISO format `YYYY-MM-DD` or keep it relative with respect to days `d`, weeks `w`, and months `m`.

When we check the key again, we should see an updated expiration date

```bash
gpg --list-keys
```

```
/home/brandon/.gnupg/pubring.kbx
------------------------------
pub   ed25519 2022-12-14 [SC] [expires: 2024-12-28]
      5F37830BFA46FF7881F47AC78DF79C3DC5FC658A
uid           [ultimate] Brandon Rozek <brozek@brandonrozek.com>
uid           [ultimate] Brandon Rozek <hello@brandonrozek.com>
sub   cv25519 2022-12-14 [E] [expires: 2023-12-14]
sub   dsa2048 2022-12-17 [S] [expires: 2023-12-14]
```

Notice that the two subkeys still have the old expiration date. We'll need to update that as well. We'll need to get their fingergrints with the following command

```bash
gpg --list-keys --verbose --with-subkey-fingerprints
```

```
gpg: enabled compatibility flags:
gpg: using pgp trust model
/home/rozek/.gnupg/pubring.kbx
------------------------------
pub   ed25519 2022-12-14 [SC] [expires: 2024-12-27]
      5F37830BFA46FF7881F47AC78DF79C3DC5FC658A
uid           [ultimate] Brandon Rozek <brozek@brandonrozek.com>
uid           [ultimate] Brandon Rozek <hello@brandonrozek.com>
sub   cv25519 2022-12-14 [E] [expires: 2023-12-14]
      D502A12A65F9997DAE4609C97DAEAD7BFFA8F9D3
sub   dsa2048 2022-12-17 [S] [expires: 2023-12-14]
      89859D1EDF70D6DC2F6BFFF226E457DA82C9F480
```

Store the fingerprints again for easy reference:

```bash
export SFPR1=D502A12A65F9997DAE4609C97DAEAD7BFFA8F9D3
export SFPR2=89859D1EDF70D6DC2F6BFFF226E457DA82C9F480
```

Extend the expiration of the subkeys:

```bash
gpg --quick-set-expire $FPR 1y $SFPR1
gpg --quick-set-expire $FPR 1y $SFPR2
```



## Updating Services

I currently allow for two ways to query my keys: OpenGPG keyserver and WKD. To update my keys on my own WKD keyserver, I followed the steps in my [tutorial on WKD](/blog/decentralized-pgp-keys-wkd). 

For OpenGPG, I followed the instructions on their [usage page](https://keys.openpgp.org/about/usage):

```bash
gpg --export your_address@example.net | curl -T - https://keys.openpgp.org 
```

## References

https://www.gnupg.org/documentation/manuals/gnupg24/gpg.1.html

https://whynothugo.nl/journal/2023/07/13/extending-an-expired-gpg-key/

https://brandonrozek.com/blog/decentralized-pgp-keys-wkd/

https://keys.openpgp.org/about/usage
