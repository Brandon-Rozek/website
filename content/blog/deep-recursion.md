---
title: "Deep Recursion"
date: 2022-11-11T14:45:17-05:00
draft: false
tags: ["Scala"]
math: false
---

In functional programming, we often look at a list in terms of its head (first-element) and tail (rest-of-list). This allows us to define operations on a list recursively. For example, how do we sum a list of integers such as `[1, 2, 3, 4]`?

```scala
def sum(l : List[Int]): Int =
    if l.size == 0 then
        0
    else if l.size == 1 then
        l.head
    else
        l.head + sum(l.tail)
```

We later learn that the `fold` version is more compact.

```scala
l.foldLeft(0)(_ + _)
```

The big question though, is how do we write this function if we allow lists to be arbitrarily nested? One example of this is the list `[[1, 2, [3, 4]], 5, [[6, 7], 8]]`

## Deep Recursion

To accomplish this, we need to make use of *deep recursion*. At its essence, we change the previous program so that it also recurses on the head of the list as well since that may be a list. 

```scala
def deep_sum(l: Int | Matchable): Int =
    if l.isInstanceOf[Int] then
        l.asInstanceOf[Int]
    else
        val ll = l.asInstanceOf[List[Int | Matchable]]
        if ll.size == 0 then
            0
        else if ll.size == 1 then
            deep_sum(ll.head)
        else
            deep_sum(ll.head) + deep_sum(ll.tail)
```

Lets trace through an example `[[1], 2]`

```
deep_sum([[1], 2])
deep_sum([1]) + deep_sum([2])
deep_sum(1) + deep_sum([2])
1 + deep_sum([2])
1 + deep_sum(2)
1 + 2
3
```

## Deep Recursion via Fold

Similar to shallow recursion, we can use the `foldLeft` function to help clean up the code a little:

```scala
def deep_sum(l : Int | Matchable): Int =
    if l.isInstanceOf[Int] then
        l.asInstanceOf[Int]
    else
        val ll = l.asInstanceOf[List[Int | Matchable]]
        ll.foldLeft(0)((c, n) => c + deep_sum(n))
```

In the above fold, `c` contains the current partial result (of type `Int`) which we can then add the recursive result of the next element of the list.

Let's trace through an example `[[1], 2]`

```
deep_sum([[1], 2])
[[1], 2].foldLeft(0)((c, n) => c + deep_sum(n))
(0 + deep_sum([1])) + deep_sum(2)
(0 + [1].foldLeft(0)((c1, n1) => c1 + deep_sum(n1))) + deep_sum(2)
(0 + (0 + deep_sum(1))) + deep_sum(2)
(0 + (0 + 1)) + deep_sum(2)
(0 + 1) + deep_sum(2)
1 + deep_sum(2)
1 + 2
3
```

## Deep Recursion via Fold/Map

In the prior example, the deep recursion and the reduction logic were combined within the same anonymous function. We can separate this out by making use of `map`.

```scala
def deep_sum(l: Int | Matchable): Int = 
    if l.isInstanceOf[Int] then
        l.asInstanceOf[Int]
    else
        val ll = l.asInstanceOf[List[Int | Matchable]]
        l.map(deep_sum).foldLeft(_ + _)
```

Intuitively, the map will apply `deep_sum` to each element of the list and returns an `Int` for each element as that's the return type of `deep_sum`. Once we have our list of integers, we can perform the fold to reduce it to a single sum. 

Lets trace through an example `[[1], 2]`

```
deep_sum([[1], 2])
[deep_sum([1]), deep_sum(2)].foldLeft(0)(_ + _)
[[deep_sum(1)].foldLeft(0)(_ + _), deep_sum(2)].foldLeft(0)(_ + _)
[[1].foldLeft(0)(_ + _), deep_sum(2)].foldLeft(0)(_ + _)
[(0 + 1), deep_sum(2)].foldLeft(0)(_ + _)
[1, deep_sum(2)].foldLeft(0)(_ + _)
[1, 2].foldLeft(0)(_ + _)
(0 + 1) + 2
1 + 2
3
```

