---
title: "Real Analysis Sequences in Haskell"
date: 2019-05-21T22:18:21-04:00
draft: false
math: true
---

In Real Analysis it is useful to look at terms of a sequence. One of the best ways I've found to do this is in believe it or not Haskell. This is mainly for these two reasons

- Support for infinite data structures

- Built-in Data Type to keep fractional precision

## Code

Let's get started, first let us define a sequence by the following:
$$
f(1) = 1, f(2) = 2, f(n) = \frac{1}{2}(f(n - 2) + f(n - 1))
$$
That is equivalent to the following haskell code:

```haskell
f :: Integral a => a -> Ratio a
f 1 = 1
f 2 = 2
f n = 0.5 * (f (n - 2) + f (n - 1))
```

Now to generate the sequence we just need to map $f$ onto the natural numbers.

```haskell
nsequence = map f [1..]
```

If you want to look at specific subsequences, such as even or odd:

```haskell
odd_generator n = 2 * n - 1
odds = map odd_generator [1..]

even_generator n = 2 * n
evens = map odd_generator [1..]
```

To look at the differences between each term:

```haskell
diff x = map (\(a, b) -> a - b) $ zip (tail x) (init x)
```

