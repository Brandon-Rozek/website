---
title: "Generate Secure Passphrases Locally with Diceware"
date: 2020-05-01T00:22:31-04:00
draft: false
tags: ["Security"]
medium_enabled: true
---

Diceware is a passphrase generator proposed by [Arnold G. Reinhold](http://diceware.com/). Passphrases contain multiple words which are chosen according to a sequence of dice rolls. Let's look at a simplified example where we have binary dice (0 or 1) and we have a wordlist of two dice rolls.

````
00	abacus
01	abdomen
10	abdominal
11	abide
````

If you roll a zero twice, then you choose the word `abacus`. If you roll a zero and then a one, you choose the word `abdomen`.

In reality, [Joseph Bonneau](https://www.eff.org/about/staff/joseph-bonneau) over at the EFF, compiled a wordlist that consists of six dice rolls with a regular 5 sided dice. Resulting in a total of $6^5$ or 7776 different [english words](https://www.eff.org/files/2016/07/18/eff_large_wordlist.txt).

Instead of rolling physical dice forever, we can use a nicely put together python package called [`diceware`](https://github.com/ulif/diceware/). It is easily installable via pip: `pip install diceware`. The README explains the security implications far better than I can. At the time of writing, it uses by default `urandom` on Linux to choose 6 words from the EFF word list from before.

```bash
diceware
```

Gave me the random passphrase "DrearilyUncorruptOutboardKneeSubzeroGumdrop".