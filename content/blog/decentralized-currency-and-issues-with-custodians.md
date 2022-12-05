---
title: "The Promise of Decentralized Currency and the Issues with Custodians"
date: 2022-12-04T19:54:58-05:00
draft: false 
tags: []
math: false
---

*Disclaimer: I'm not an active participant in the Bitcoin community and the comments of this post are from an outside perspective.*

[FTX, one of the largest crypto exchanges](https://en.wikipedia.org/wiki/FTX_(company)), collapsed last month taking many people's investments and savings with them. Investigations are currently underway for if FTX [illegally lent customer funds to a partner company Alameda research](https://www.nytimes.com/article/ftx-bankruptcy-crypto-collapse.html), the beginning of the strategies used by FTX to hide their insolvency.

As this is among a [series of collapses](https://www.nerdwallet.com/article/investing/crypto-winter), it has people skeptical on the value of Bitcoin. From my memory, the last major collapse of similar magnitude is that of [Mt. Gox](https://en.wikipedia.org/wiki/Mt._Gox) in 2014. Even with these collapses, I however, don't see this as the reason to avoid Bitcoin altogether.[^1]

## Who owns the Bitcoin?

When you buy Bitcoin off any of these exchanges you don't **own** the Bitcoin. What do I mean by this? Well let's look at a higher level on how Bitcoin works.

From the original whitepaper:

> Each owner transfers the coin to the next by digitally signing a hash of the previous transaction and the public key of the next owner and adding these to the end of the coin.

What do you need then to perform the transaction?

- Your private key
- Destination's public key
- Public ledger which denotes the funds associated with your account 

Now where is your private key stored on these exchanges? It terms out, as a user of their service, you don't have access to it. Instead you're granting them permission to handle the money on your behalf, what you receive is much like an IOU.

Now we trust banks to hold our funds, how is this different? Banks are FDIC/NCUA insured. This means that you are guaranteed to receive $250,000 per insured bank, per depositor, per account ownership category. If your bank ever goes bankrupt, all your money does not go with it.

What this is more similar to is the PayPal model. [PayPal is itself not a bank](https://www.forbes.com/advisor/banking/paypal-as-bank-account/), so leaving money in a PayPal acount is not protected under FDIC insurance. In fact, they are also under a [class action lawsuit for freezing customer funds](https://arstechnica.com/tech-policy/2022/01/paypal-stole-users-money-after-freezing-seizing-funds-lawsuit-alleges/). Nothing says that you don't own the money more than not being able to access it.

## Bitcoin is meant to be a decentralized currency

We really shouldn't be holding large amounts of Bitcoins with these *custodians*. Instead, each person should control their own private keys. We can do this through a non-custodial wallet. This requires the generation of private keys which are often done through *seed words*. I won't go into detail on this as per my disclaimer above, however, I find [bitcoiner.guide](https://bitcoiner.guide/) to be a nice and honest resource.

## Do not confuse ownership with privacy

Often purchasing Bitcoin from an exchange passes through a *Know Your Customer* (KYC) organization. Simply moving the money off a custodial account into your own Bitcoin wallet does not mean that it can not be associated with you. [Bitcoin transactions are public information by design](https://www.blockchain.com/explorer/blocks/bch). In terms of controlling your privacy, I can't provide much advice. However, look into Bitcoin Escrow services to facillitate anonymous purchasing/selling as well as the [coin join techinque](https://bitcoinmagazine.com/technical/a-comprehensive-bitcoin-coinjoin-guide) for granting some plausible deniability.




[^1]: I understand other arguments more such as the un-sustainability of the *Proof-of-work* protocol.
