---
title: "Hashing Based on Word (Emoji?) Lists"
date: 2024-12-30T19:13:35-05:00
draft: false
tags: []
math: true
medium_enabled: false
---

When I go to download Fedora Workstation 41, it gives me an option to verify the ISO download with a SHA-256 checksum.

```
a2dd3caf3224b8f3a640d9e31b1016d2a4e98a6d7cb435a1e2030235976d6da2
```

The idea is that when I download the ISO, I run

```bash
sha256sun Fedora-Workstation-Live-x86_64-41-1.4.iso
```

The output of the command should match the given checksum. If not, I should assume that I have a fraudulent ISO.[^1]

[^1]: You might ask, how do we know that the checksum hasn't been tampered with? Fedora's solution is PGP-signatures, but that's outside the scope of this post.

SHA-256 is one particular [*Cryptographic hash function*](https://en.wikipedia.org/wiki/Cryptographic_hash_function). There are many others, but these algorithms are typically used for some form of verification. These algorithms have the following properties:

- **Deterministic**:  When you run it on the same input, you get the same output.
- **Fixed-Length:** Inputs can be as long as you want, but the output has a fixed-length.
- **Pre-image Resistant**: All inputs are equally likely to produce a particular hash value.
- **Second Pre-Image Resistant**: All inputs are equally likely to produce the same hash value as a particular input.
- **Collision Resistant**: It's difficult to find any two messages that have the same hash value.

I won't get into these properties in this post. Feel free to read the Wikipedia article linked above to learn more.

Another example of a verification task is password checking. The idea is that (hopefully most) websites don't actually store your passwords, but a hash value of them on their servers. When you send in your password, they then hash it and make sure the hash values match.

**Please don't use SHA-256 for password checking.** Unfortunately, many people use short/simple passwords, and re-use them across multiple websites. If an attacker gets a hold of your password hash database, they can run the hash function on a bunch of common passwords and see if any of those hashes match what's inside the database. Best practices evolve over time, so please do your research when implementing authentication.

Krishna wrote a [blog post](https://chittur.dev/cs/2020/04/11/readable-hashes.html) a few years ago advocating for the use of *human-readable* hash values. Instead of using a random sequence of characters, why don't we use a random sequence of words instead?

As a community, we have agreed on what possible characters a SHA-256 checksum can consist of. That is, alphanumeric characters a-z and 0-9. However, *we don't agree on what words we should use*.

Lifting from Krishna's blog post, there are [multiple](https://github.com/singpolyma/mnemonicode) [readable](https://tools.ietf.org/html/rfc1751) [hash](https://github.com/fpgaminer/hash-phrase) ideas out there. They each use different wordlists. Even Krishna's approach uses a different one!

I'll go over a general approach on how to implement a hash function for any arbitrary wordlist. Then I'll argue, that we should consider using Emojis for our wordlist.

### A general approach to hashing with word lists

Instead of directly worrying about how to create a hash function, we're going to piggy-back off an existing one.  For example, consider the SHA-256 algorithm. This takes an input and produces a 256-bit number.

Given a wordlist of $N$ words, we want to produce a sequence of words that captures at least the amount of information within a 256-bit number. The number of bits that a word represents in our wordlist is:
$$
wbits = \lfloor log_2(N) \rfloor
$$
From this, we can derive how many words we need to capture a 256-bit number
$$
outlen = \lceil 256 / wbits \rceil
$$
Consider an arbitrary input `x` and hash it to create `h`

```python
h = int(hashlib.sha256(x).hexdigest(), 16) 
```

For the UTF-8 encoded string `"test"`, we'll get the following binary representation:

```
1001111110000110110100001000000110001000010011000111110101100101100110100010111111101010101000001100010101011010110100000001010110100011101111110100111100011011001010110000101110000010001011001101000101011101011011000001010110110000111100000000101000001000
```

To determine which word from the word lists to use, we'll consider binary sequences of length `wbits`. Since 256 might not be divisible by `wbits`, we might need to pad a certain number of zeros at the end.

```bash
bits_needed = (math.ceil(256 / outlen) * outlen) - 256
h = h << bits_needed
```

For sake of example, let's say that `wbits` is equal to 11. Then the first binary sequence is `10011111100`. This corresponds to the 1276th word in our word list.

Iterate through all these subsequences to have a list of indices:

```python
indices = []
for i in range(outlen):
    num = (h >> (wbits * i)) & (2**wbits - 1)
    indices.append(num)
```

Consider the word list `wordlist`, we can use the indices to print out the hashed version of our input using the word list!

```python
words = [wordlist[i] for i in indices]
print(" ".join(words))
```

The full script is located at the bottom of this post.

### Which wordlist should I use?

The smaller our word list length $N$ is, the more words we'll need to output for the hash. Ideally, we use a large word list. As discussed before, there's many different opinions on what properties a word list should have. Some believe that a word list should only contain [easy-to-pronounce](https://github.com/singpolyma/mnemonicode) words. Many don't want profanity in their word lists.

Joseph Bonneau wrote a [blog post](https://www.eff.org/deeplinks/2016/07/new-wordlists-random-passphrases) describing all the criteria he used when crafting his choice of 7776 words. The EFF endorses this word list for use in password generation, and the [diceware](https://github.com/ulif/diceware) Python package also uses this list.

What's important though, is that both parties agree on what word list to use.

When designing a word list, one issue to look out for is the [Prefix Code Problem](https://en.wikipedia.org/wiki/Prefix_code). Some words are concatenations of other words, for example: rainbow, today, sunflower, etc. If you don't use a delimiter between words, then you'll lose information since we can't distinguish whether it's multiple words or just one word.

Returning to the EFF word list, here's how we can obtain the word list as of the time of writing:

```bash
curl https://www.eff.org/files/2016/07/18/eff_large_wordlist.txt | cut -f2 > eff_wordlist.txt
```

In order to capture the 256-bit hash, we need to use 22 words from the EFF word list. The hash for the UTF-8 encoded version of "test" is:

```
duress amiss antler atop item illicitly blimp anchor gigahertz consoling chance atonable frugality hardhead freeing bust crowd drool editor earful detective fiction
```

Words are nice and all. But what about Emojis? The Unicode Consortium maintains a list of [thousands of emojis](https://unicode.org/emoji/charts/full-emoji-list.html). Like words, emojis are very easy for our eyes to parse.

As of the time of writing, we're at version 16 of the Emoji character list.  Here's a crude parser for getting a list of emojis.

```bash
curl https://unicode.org/Public/emoji/16.0/emoji-test.txt | grep -v "^#" | grep -oP '#\s*\K.*?(?=\s*E)' > emojis.txt
```

This produces a list of 5042 emojis. Similarly, to capture a 256-bit hash, we'll need to use 22 emojis. For the UTF-8 encoded version of "test", the hash is

```
🧍🏼‍♂️ 💜 🫷 🫵🏽 👩🏿‍❤‍👩🏾 👨🏼‍❤️‍👨🏼 👨🏾 💤 🤹 🧑🏿‍🎨 🤦🏼‍♂ 🫵🏼 🤸🏾 👨🏽‍❤️‍💋‍👨🏼 🚴🏿‍♂️ 🙎🏿‍♀️ 💂‍♀ 🚶🏾‍♀️‍➡️ 🧎🏽‍♀️‍➡ 🧎🏾 🧙🏿‍♂ 🏄🏻‍♂️

```

Does your browser show all the emojis?

While I'm advocating for the use of emojis, there are two problems that I currently recognize:

- New emojis get introduced regularly. Luckily the dataset is versioned, so you can state to verify using the version 16 set.
- Not all applications and fonts support newer emojis. I use Konsole with Noto Sans and "🫩" is not recognized.

Though I feel that emojis are richer than a standard English based word list. Also, it's friendly to those who don't speak English as well!

The full script from before:


```python
import argparse
import hashlib
import math

parser = argparse.ArgumentParser(description="Create a hash from a wordlist")
parser.add_argument("wordlist", type=str, help="Path to wordlist")
args = vars(parser.parse_args())

wordlist = []
# File must have one word per line
with open(args['wordlist']) as f:
    wordlist = f.read().splitlines()

assert len(wordlist) > 0

# Number of bits we can use to index the wordlist
wlbits = math.floor(math.log(len(wordlist)) / math.log(2))
outlen = math.ceil(256 / wlbits)
bits_needed = (math.ceil(256 / outlen) * outlen) - 256

data = input("")

sha256_data = hashlib.sha256(data.encode("utf-8"))
encoded_data = int(sha256_data.hexdigest(), 16) << bits_needed

indices = []
for i in range(outlen):
    num = (encoded_data >> (wlbits * i)) & (2**wlbits - 1)
    indices.append(num)

words = [wordlist[i] for i in indices]
print(" ".join(words))

```
