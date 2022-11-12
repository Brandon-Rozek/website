---
title: "Fold Not Only Reduces"
date: 2022-11-09T15:15:10-05:00
draft: false
tags: ["Functional Programming", "Scala", "Haskell"]
math: false
---

One misconception when first learning about fold is that it takes a list of elements of a certain type (`List[T]`) and "reduces" it to a single item of type `T`.

This misconception is aided by one of the most common fold examples: summing a list.

Scala Example:

```scala
List(1, 2, 3, 4, 5).foldLeft(0)((c, n) => c + n)
// Returns 15
```

Haskell Example:

```haskell
foldl (+) 0 [1,2,3,4,5]
-- Returns 15
```

However, let us look more closely at the type signature of `foldLeft` on a list of type `X`.

Haskell:

```
(B -> X -> B) -> B -> [X] -> B
```

Scala:

```
(id: B)(op: (B, X) => B): B
```

There are a few things we can note here:

- The return type is not influenced by the list type `X` at all.
- The return type must match the type of the id of the fold.
- The operation takes two arguments, with the first type matching the id/start (`B`) and the second type matching the type within the list (`X`)

To show an example of how we don't need to "reduce", let's return the elements of a list that's greater than 5.

Scala Example:

```scala
List(5, 7, 1, 8, 9, 3).foldLeft(List.empty[Int])((c, n) => if n > 5 then c :+ n else c)
// Returns List(7, 8, 9)
```

Haskell Example:

```haskell
l5 c n if n > 5 then c ++ [n] else c
foldl l5 [] [5, 7, 1, 8, 9, 3]
-- Returns [7,8,9]
```

