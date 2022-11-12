---
title: "Memoization in Scala"
date: 2022-11-12T11:49:51-05:00
draft: false
tags: ["Scala"]
math: false
---

In a [recent post](/blog/corecursion-unfold-infinite-sequences/), I talked about how corecursion is a great solution for removing redundant calculations. However if we're sticking to a recursive approach, one way we can reduce redundancies is to use memoization. The idea here is that we save prior computations in some data structure and refer to them if requested.

 [Pathikrit on StackOverflow](https://stackoverflow.com/a/36960228) provided a great solution for Scala using hashmaps:

```scala
import scala.collection.mutable
def memoize[I, O](f: I => O): I => O = new mutable.HashMap[I, O]() {self =>
  override def apply(key: I) = self.synchronized(getOrElseUpdate(key, f(key)))
}
```

If the input is already a key in the hashmap, then we return its value. Otherwise we calculate the output via `f` and update the hashmap.

Now lets memoize say the Fibonacci sequence

```scala
val fib : Int => Int  = memoize {
    case 0 => 0
    case 1 => 1
    case n => fib(n - 1) + fib(n - 2)
}
```

Calling `fib(5)` returns `5`. However, we can also see the saved computations by analyzing the hashmap `fib`.

```
HashMap(0 -> 0, 1 -> 1, 2 -> 1, 3 -> 2, 4 -> 3, 5 -> 5)
```



