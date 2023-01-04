---
title: "Decentralized PGP Keys with WKD"
date: 2023-01-04T09:06:38-05:00
draft: false 
tags: ["GPG/PGP"]
math: false
---

After creating a PGP key, it is common to distribute it to various keyservers. However, anyone can upload to these keyservers impersonating someone else. One solution is to use a decentralized identities approach, however, if your email is on your own domain that you tell every soul about, why not have your own website host the key? This is where the Web Key Directory (WKD) protocol comes in.

## Setting up WKD

To start we need to create a new folder on our webserver:

```bash
mkdir .well-known/openpgpkey/hu
```

In it, add an empty policy file

```bsah
touch .well-known/openpgpkey/hu/policy
```

Now we need to add our key to the folder. The key needs to be stored in the file named after the email's WKD hash. We can get this hash through the following command:

```bash
gpg --with-wkd-hash --fingerprint brozek@brandonrozek.com
```

Replacing my email with yours. At the current moment, this returns the following for me:

```
pub   ed25519 2022-12-14 [SC] [expires: 2023-12-14]
      5F37 830B FA46 FF78 81F4  7AC7 8DF7 9C3D C5FC 658A
uid           [ultimate] Brandon Rozek <brozek@brandonrozek.com>
              o1dbwkdx683fduwgzmrbwa3yip41frdn@brandonrozek.com
uid           [ultimate] Brandon Rozek <hello@brandonrozek.com>
              im4cc8qhazwkfsi65a8us1bc5gzk1o4p@brandonrozek.com
```

The string starting with`o1dbwk` is the WKD hash for `brozek@brandonrozek.com` and the string starting with `im4cc8qh` is the WKD hash for `hello@brandonrozek.com`.

Let's store that hash in `$WKD`

```bash
export WKD="o1dbwkdx683fduwgzmrbwa3yip41frdn"
```

The WKD specification says to upload the non-armored (binary) version of our key.

```bash
gpg --no-armor --export brozek@brandonrozek.com > .well-known/openpgpkey/hu/$WKD
```

After uploading it to our webserver, it needs to be configured with the right content type and access control headers.

In Nginx:

```nginx
location /.well-known/openpgpkey {
    default_type application/octet-stream;
    add_header Access-Control-Allow-Origin "*";
}
```

Now we can check our setup using the website:

https://metacode.biz/openpgp/web-key-directory

## Using WKD

Many applications currently support WKD, though I'll show how we can use `gpg` to search for someone's key.

```bash
gpg --auto-key-locate wkd --locate-key brozek@brandonrozek.com
```

This will not only locate but import the key into our keystore.

With WKD, we didn't have to trust anyone but the DNS provider in order to retrieve the key. The biggest downside with this approach, however, is that most people do not have an email on their own domain. Since nowadays, many people use gmail as their primary provider, they will have to fallback to using a different approach for distributing their keys.

## References

- https://shibumi.dev/posts/how-to-setup-your-own-wkd-server/
- https://www.sindastra.de/p/1905/how-to-set-up-pgp-wkd-web-key-directory
- https://shivering-isles.com/Lets-discover-OpenPGP-keys
- https://wiki.gnupg.org/WKD
