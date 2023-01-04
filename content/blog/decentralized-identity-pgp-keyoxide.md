---
title: "Decentralized Identities with PGP Annotations and Keyoxide"
date: 2023-01-04T09:00:14-05:00
draft: false
tags: ["PGP"]
math: false
---

Under asymmetric encryption, for you to send me a message that only I can read you would need to encrypt the message with my public key. I then would have a corresponding private key that can decrypt the message. Public keys are then usually stored onto keyservers for others to query. When querying for a key, how do you know that the public key actually belongs to me? It turns out, you can't since anyone can upload a key pretending to be me.

What's the solution? When PGP first came around, it was built around the [Web of Trust](https://en.wikipedia.org/wiki/Web_of_trust) concept. The idea is that people would go to key-signing parties and verify in person that they are who they say they are. From a graph would be built out showing who verified who. Sadly this idea didn't take off. A very small segment of the population attends key signing parties.

## Keybase

In 2014, [Keybase](https://keybase.io/) was created to help solve this issue. The concept behind it is that we have other identities in the web, and by associating a keybase profiles to these identities others can have a strong confidence on who they are speaking to.

For example, I own the website brandonrozek.com and am known as [@brozek@fosstodon.org](https://fosstodon.org/@brozek) on Mastodon. On those platforms, I would create a post using the private key on keybase which claims that I own the user profile on keybase. Similarly on keybase I would link to my website and mastodon profile to say that I claim those.

For a while, this was working great. Then in 2019 the following article comes out of their blog:

> Keybase + Stellar is live for everyone!
>
> Source: https://keybase.io/blog/keybase-stellar-launch

The promotion of cryptocurrency makes you wonder how they are doing financially. Then in 2020, we see:

> Keybase joins Zoom
>
> Source: https://keybase.io/blog/keybase-joins-zoom

Upon further reflection, several questions arise:

- Why am I depending on Keybase to show which users I'm connected to? Ideally, this should be decentralized.
- Keybase holds access to the private key. While this makes the user experience easier since I don't need to worry about those details. We should be encouraging people to hold their private keys instead.

What's a great alternative to Keybase then? This is where [Keyoxide](https://keyoxide.org/) comes in.

## Keyoxide & PGP Notations

Yarmo Mackenbach wanted to create a project that's decentralized in nature. This means that Keyoxide doesn't hold the keys. Instead it depends on either:

- Web Key Directory (WKD) protocol where the keys are stored on your own server belonging to the domain.
- HTTP Keyserver Protocol (HKP) where Keyoxide queries keys.openpgp.org

Within the key you upload, you can add a PGP notation. This allows us to provide additional text on what accounts we own. 

For example the notation of:

```
proof@ariadne.id=dns:brandonrozek.com?type=TXT
```

claims that I own the domain `brandonrozek.com`.

To provide the necessary backlink, the [Keyoxide documentation](https://docs.keyoxide.org/service-providers/dns/) says to create a TXT record with my PGP fingerprint.

```
openpgp4fpr:5F37830BFA46FF7881F47AC78DF79C3DC5FC658A
```

Notice how nowhere in the process do we reference Keyoxide or their servers. This only depends upon the keys that I upload onto the Internet and the appropriate backlinks. Keyoxide in this case, only serves as a validator, making sure that the links exist.

My Keyoxide profile: https://keyoxide.org/wkd/brozek%40brandonrozek.com

In fact, Keyoxide is [open source](https://codeberg.org/keyoxide/) meaning that anyone can host their own instance to perform the validation checks.
