---
title: "Cryptographic Games"
date: 2020-01-13T21:35:09-05:00
draft: false
---

When analyzing cryptographic algorithms, we characterize the strength of the crypto-system by analyzing what happens in various crypto games. Below are a couple examples of crypto games used in literature.

Actors typically involved in crypto games:

| Actor      | Role                                                       |
| ---------- | ---------------------------------------------------------- |
| Oracle     | Encrypts a given message.                                  |
| Challenger | Sets up the game between the oracle and adversary.         |
| Adversary  | Sends messages to the oracle and makes a guess at the end. |



## Left-Right Game

Here we will have two oracle's `left` and `right` both with a random key $k$.

The challenger will create a random bit $b$ which is either $0$ or $1$.

If the bit is $0$, then the adversary will send messages to `left`. Otherwise, the adversary will send messages to `right`.

After a certain number of interactions the adversary needs to guess which oracle it is talking to.

We define the adversary's advantage by the distance the probability is away from $\frac{1}{2}$.
$$
advantage = |p - \frac{1}{2}|
$$
Why the absolute value? Well if we only guess correctly $10\%$ of the time, then we just need to invert our guess to be correct $90\%$ of the time.

```
Generate key for both oracles
Generate random bit b
while game not done:
  advesary generates message m
  if b = 0:
    send m to left oracle
    receive c from left oracle
  else:
    send m to right oracle
    receive c from right oracle
Adversary guesses whether b = 0 or 1
```

## Real-Random Game

This game is very similar to the last one except one of the oracle's only produces random bitstrings.

An oracle is initialized with a random key $k$ and the challenger creates a random bit $b$.

If $b = 0$, then the adversary will send messages to the oracle with the proper encryption function and will receive ciphertexts. Otherwise, the adversary will send messages to the random bitstring generator.

At the end of the game, the adversary needs to guess whether its talking to a proper oracle or a random bitstring generator.

The same metric `adversary's advantage` is used to characterize the strength of a crypto-system as the last one.

```
Generate key for both oracles
Generate random bit b
while game not done:
  advesary generates message m
  if b = 0:
    send m to proper oracle
    receive c from proper oracle
  else:
    send m to random oracle
    receive random bitstring c from random oracle
Adversary guesses whether b = 0 or 1
```

## Random Function - Random Permutation Trick

One trick that we can use in proofs is to say that two procedures are the same up to a certain point when it diverges.

Let us define $f$ to be some function that given a bitstring $X$ produces a random bitstring $Y$.

Now, $image(f)$ is initially undefined since we don't know which bitstrings will be randomly generated.

However, as we calculate $Y$ we will store it to build up $image(f)$.

At some point, we'll generate $Y$ that already exists in $image(f)$. In that moment we will split based off of whether the procedure is a random function or random permutation.

If random function, then just return the same $Y$ and end the procedure. Otherwise, return a random bitstring outside of the $range(f)$ and end the procedure.

```
Initialize function f with range(f) empty
Generate different random bitstring X
While f(X) not in range(f):
  Add f(X) to range(f)
  Generate different random bitstring X
If random function:
  return f(X)
Else:
  return random bitstring Y not in range(f)
```

