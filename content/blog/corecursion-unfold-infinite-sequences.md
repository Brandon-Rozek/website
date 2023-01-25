---
date: 2022-11-12 10:45:04-05:00
draft: false
math: true
medium_enabled: true
medium_post_id: edd1ef8ee314
tags:
- Scala
- Functional Programming
title: Corecursion, Unfold and Infinite Sequences
---

Recursion takes a large problem and breaks it down until it reaches some base cases. One popular example, is the factorial function.

```scala
def fact(x: Int): Int =
    if x == 0 then
        1
    else if x == 1 then
        1
    else
        x * fact(x - 1)
```

Though we can similarly arrive at the answer by starting at the base case `1` and multiplying until we reach `x`. This is called co-recursion.

```
1 * 2 * ... * x
```

`Unfold` allows us to create sequences given some initial state and a function that takes some state and produces a value for the sequence. For the factorial function, we want to keep track of in our state the last factorial computed and the current index. `(lastFact, currInd)`. 

Therefore, our initial state is `(1, 0)`.

```scala
val fact_seq = () => Iterator.unfold((1, 0))((x, y) => Some(
    x, // currFact
    (x * (y + 1), y + 1) // (nextFact, nextInd)
))

val fact = (x: Int) => fact_seq().take(x + 1).toList.last
```

 Let's trace an execution of `fact(4)`.

```
fact(4)
Iterator.unfold((1, 0))((x, y) => Some((x, (x * (y + 1), y + 1)))).take(5).toList.last
States: (1, 0) -> (1, 1) -> (2, 2) -> (6, 3) -> (24, 4).....
[1, 1, 2, 6, 24, ...].take(4).toList.last
[1, 1, 2, 6, 24].last
24
```

Now why is this useful when maybe the recursive version can seem cleaner? Co-recursion and in turn unfolding can help remove redundancies. Let's look at the Fibbonaci sequence for an example. The recursive version would be as follows:

```scala
def fib(n : Int): Int =
    if n == 0 then
        0
    else if n == 1 then
        1
    else
        fib(n - 1) + fib(n - 2)
```

Now let's trace through an execution of `fib(4)`

```
fib(4)
fib(3) + fib(2)
(fib(2) + fib(1)) + fib(2)
((fib(1) + fib(0)) + fib(1)) + fib(2)
((1 + fib(0)) + fib(1)) + fib(2)
((1 + 0) + fib(1)) + fib(2)
(1 + fib(1)) + fib(2)
(1 + 1) + fib(2)
2 + fib(2)
2 + (fib(1) + fib(0))
2  + (1 + fib(0))
2 + (1 + 0)
2 + 1
3
```

Notice how there are many redundant calculations, for example `fib(2)` is evaluated twice separately in line 3 above.

Now lets look at how `unfold` helps.  For our state, we need to keep track of the last two evaluations. Therefore, we can represent our state as `(currentAnswer, nextAnswer)`.

```scala
val fib_seq = () => Iterator.unfold((0, 1))((x, y) => Some(x, (y, x + y)))
val fib: (Int => Int) = (n) => fib_seq.take(n + 1).toList.last
```

Tracing through `fib(4)`

```
fib(4)
Iterator.unfold((0, 1))((x, y) => Some(x,(y, x + y))).take(5).toList.last
State: (0, 1) -> (1, 1) -> (1, 2) -> (2, 3) -> (3, 5)
[0, 1, 1, 2, 3, ...].take(5).toList.last
[0, 1, 1, 2, 3].last
3
```

## Small Unfold Examples

To get a better handle of `unfold`. Here are three examples:

**(1) Build an iterator from start to infinity with a step size of `step`**

Built-in way in Scala:

```scala
Iterator.from(start, step)
```

Using `unfold`

```scala
val fromStep: ((Int, Int) => Iterator[Int]) = (n, step) => Iterator.unfold(n)(x => Some((x, x + step)))
```

**(2) Build an infinite sequence of even numbers**

Using from and map:

```scala
val evens = Iterator.from(0).filter(_ % 2 == 0)
```

Using `fromStep` in (1)

```scala
val evens = fromStep(0, 2)
```

Using `unfold`

```scala
val evens = Iterator.unfold(0)(x => Some((x, x + 2)))
```

**(3)  Build a countdown from $n$ to $0$**

Notice how the function within `unfold` needs to return an `Option`. If the returned option is `None` then the sequence is terminated.

```scala
val countdown = (n: Int) => Iterator.unfold(n)(x => if x == -1 then None else Some((x, x - 1)))
```

**(4) Repeat an element forever**

For this example, we don't need to carry any state throughout hte computation.
```scala
val repeat: (Int => Iterator[Int]) = (n) => Iterator.unfold(None)(_ => Some(n, None))
```

## Recursive Sequences

In the past, [I've written](/blog/haskellrealsequences/) about analyzing sequences from real analysis within Haskell. Within it, I was looking at the following sequence:
$$
f(1) = 1, f(2) = 2, f(n) = \frac{1}{2}(f(n - 2) + f(n - 1))
$$
The technique I described in that post is to build out the function `f` and then map it to the natural numbers. In Scala that would look like:

```scala
val f: (Int => Double) = n => if n == 1 then 1.0 else if n == 2 then 2.0 else 0.5 * (f(n - 2) + f(n - 1))
val f_sequence = Iterator.from(1).map(f)
```

However as mentioned in prior in this post, this methodology is suboptimal since there will be many repeated computations. 

Corecursion and unfold comes to the rescue again. For recursive sequences, we can make the state the base cases `(1.0, 2.0)`.

```scala
val f_sequence = () => Iterator.unfold((1.0, 2.0))((x1, x2) => Some(
    x1,
    (x2, 0.5 * (x1 + x2))
))
```

We can get a good guess at where this sequence converges by looking at the $100^{th}$ element.

```scala
f_sequence().take(100).toList.last
// 1.6666666666666665
```

If you want to learn more about unfold or see a different take, then the following two blog posts helped me craft this one:

https://blog.genuine.com/2020/07/scala-unfold/

https://john.cs.olemiss.edu/~hcc/csci555/notes/FPS05/Laziness.html