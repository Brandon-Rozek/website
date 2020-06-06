---
title: "GPG Card"
date: 2020-06-05T17:39:51-04:00
draft: false
tags: []
---

I have a Yubikey hardware token and one of my favorite use cases is the GPG support. This gives you the use cases of signing, encrypting, and authenticating all in one module. This post will describe quickly setting it up.

```bash
gpg --card--edit
```


To edit the keys we need to be in admin mode.
```
gpg/card> admin
Admin commands are allowed
```

First thing that'll be good to configure is the name of the cardholder.
```
gpg/card> name
Cardholder's surname: Rozek
Cardholder's given name: Brandon
```

You can also set the language preferences.
```
gpg/card> lang
Language preferences: en
```

Now to configure the three different keys, we need to decide on an algorithm. There is a great [blog post by Cloudflare](https://blog.cloudflare.com/a-relatively-easy-to-understand-primer-on-elliptic-curve-cryptography/) describing RSA and ECC in detail. Including their pros and cons.
```
gpg/card> key-attr
Changing card key attribute for: Signature key
Please select what kind of key you want:
   (1) RSA
   (2) ECC
Your selection? 1
What keysize do you want? (2048) 4096
The card will now be re-configured to generate a key of 4096 bits
Changing card key attribute for: Encryption key
Please select what kind of key you want:
   (1) RSA
   (2) ECC
Your selection? 1
What keysize do you want? (2048) 4096
The card will now be re-configured to generate a key of 4096 bits
Changing card key attribute for: Authentication key
Please select what kind of key you want:
   (1) RSA
   (2) ECC
Your selection? 1
What keysize do you want? (2048) 4096
The card will now be re-configured to generate a key of 4096 bits
```

Once configured, we finally generate the keys. I usually recommend a shelf live of a year for keys. I think of security as a conscious effort, and this forces us to reconsider this again in the future.
```
gpg/card> generate
Make off-card backup of encryption key? (Y/n) n

Please specify how long the key should be valid.
         0 = key does not expire
      <n>  = key expires in n days
      <n>w = key expires in n weeks
      <n>m = key expires in n months
      <n>y = key expires in n years
Key is valid for? (0) 1y
Key expires at Fri 26 June 2021 11:20:37 PM EDT
Is this correct? (y/N) y
```

Finally, add some metadata about the key.
```
GnuPG needs to construct a user ID to identify your key.

Real name: Brandon Rozek
Email address: brandon@therozek.com
Comment: 
You selected this USER-ID:
    "Brandon Rozek <brandon@therozek.com>"

Change (N)ame, (C)omment, (E)mail or (O)kay/(Q)uit? O
```

And we're done! Now you have three keys on your smartcard for signing, encrypting, and authenticating.
```
gpg/card> quit
```



