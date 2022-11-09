---
title: "Different Views of Fold and Their Combinations"
date: 2022-11-09T17:45:26-05:00
draft: false
tags: []
math: true
---

Fold is a functional programming pattern that operates over some sequence with a binary operation and a starting value. There are two variants:

FoldLeft: Performs the binary operation from the left of the sequence to the right.

```scala
List(1, 2, 3, 4).foldLeft(0)(_ + _)
// ((((0 + 1) + 2) + 3) + 4)
// 10
```

FoldRight: Performs the binary operation from the right of the sequence to the left.

```scala
List(1, 2, 3, 4).foldRight(0)(_ + _)
// (1 + (2 + (3 + (4 + 0))))
// 10
```

The two fold variants only return the same solution if the function being applied is associative. Which is the case for integer addition above.

## Definition and the Two Views

Definition of `foldLeft` within Scala:

```scala
def foldLeft[B](z: B)(op: (B, A) => B): B = this match {
  case seq: IndexedSeq[A @unchecked] => foldl(seq, 0, z, op)
  case _ =>
    var result = z
    val it = iterator
    while (it.hasNext) {
      result = op(result, it.next())
    }
    result
  }

def foldl[B](seq: IndexedSeq[A], start: Int, z: B, op: (B, A) => B): B = {
    @tailrec def loop(at: Int, end: Int, acc: B): B =
      if (at == end) acc
      else loop(at + 1, end, op(acc, seq(at)))
    loop(start, seq.length, z)
  }
```

Notice that this includes both a recursive and iterative definition within one function! Since most people start off by learning loops, let's focus on the iterative implementation.

```scala
var result = z
while (it.hasNext) {
    result = op(result, it.next())
}
```

## Combining Folds

When building out complex functions we may want to loop multiple times:

- While loops next to each other ($n_1 + n_2$ complexity)
- While loop within a while loop ($n_1 * n_2$ complexity)

### $n_1 + n_2$ Complexity

The following is an example of this class of algorithms.

Given a list of words, title case each word and combine them into a single sentence.

```scala
val l1 = List("steve", "is", "doing", "great")
val title = (s: String) => s.substring(0, 1).toUpperCase + s.substring(1)

val it1 = l1.iterator
var id1 = List.empty[String]

while (it1.hasNext) {
    id1 = id1 :+ title(it1.next())
}

val it2 = id1.iterator
var id2 = ""
while (it2.hasNext) {
    id2 = id2 + " " + it2.next()
}
```

Converting to fold solution:

```scala
val l1 = List("steve", "is", "doing", "great")
val title = (s: String) => s.substring(0, 1).toUpperCase + s.substring(1)
val id1 = List.empty[String]
val id2 = ""

l1.foldLeft(id1)((c, n) =>
	c :+ title(n)
).foldLeft(id2)((c, n) =>
	c + " " + n
)
```

### $n_1 * n_2$ Complexity

An example of this class of programs is the [Cartesian product](https://en.wikipedia.org/wiki/Cartesian_product)
$$
(1, 2, 3) \times (4, 5,6) \rightarrow ((1,4), (1,5), (1,6), \dots, (3,4), (3,5), (3,6))
$$
Iterative Implementation:

```scala
val listInput1 = List(1,2,3)
val listInput2 = List(4,5,6)

var id_outer = List.empty[(Int, Int)]
val it1 = listInput1.iterator

while (it1.hasNext) {
    var id_inner = List.empty[(Int, Int)]
    val n1 = it1.next()
    val it2 = listInput2.iterator
    while (it2.hasNext) {
        val n2 = it2.next()
        result_inner = result_inner :+ (n1, n2)
    }
    result = result ++ result_inner
}
```

Converting to fold solution:

```scala
val l1 = List(1,2,3)
val l2 = List(4,5,6)
val id_outer = List.empty[(Int, Int)]
val id_inner = List.empty[(Int, Int)]

l1.foldLeft(id_outer)((c1, n1) =>
    c1 ++ l2.foldLeft(id_inner)((c2, n2) =>
        c2 :+ (n1, n2)
    )
)
```
