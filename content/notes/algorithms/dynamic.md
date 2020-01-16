# Dynamic Programming

The book first goes into talking about the complexity of the Fibonacci algorithm

```
RecFibo(n):
  if n = 0
    return 0
  else if n = 1
    return 1
  else 
    return RecFibo(n - 1) + RecFibo(n - 2)
```

It talks about how the complexity of this is exponential.

"A single call to `RecFibo(n)` results in one recursive call to `RecFibo(n−1)`, two recursive calls to `RecFibo(n−2)`, three recursive calls to `RecFibo(n−3)`, five recursive calls to `RecFibo(n−4)`"

Now consider the memoized version of this algorithm...

```
MemFibo(n):
  if n = 0
    return 0
  else if n = 1
    return 1
  else 
    if F[n] is undefined:
      F[n] <- MemFibo(n - 1) + MemFibo(n - 2)
    return F[n]
```

This actually makes the algorithm run in linear time!

![1564017052666](/home/rozek/Documents/StudyGroup/Algorithms/1564017052666.png)

Dynamic programming makes use of this fact and just intentionally fills up an array with the values of $F$.

```
IterFibo(n):
  F[0] <- 0
  F[1] <- 1
  for i <- 2 to n
    F[i] <- F[i - 1] + F[i - 2]
  return F[n]
```

Here the linear complexity becomes super apparent!

<u>Interesting snippet</u>

"We had a very interesting gentleman in Washington named Wilson. He was secretary of Defense, and he actually had a pathological fear and hatred of the word *research*. I’m not using the term lightly; I’m using it precisely. His face would suffuse, he would turn red, and he would get violent if people used the term *research* in his presence. You can imagine how he felt, then, about the term *mathematical*.... I felt I had to do something to shield Wilson and the Air Force from the fact that I was really doing mathematics inside the RAND Corporation. What title, what name, could I choose?"



Dynamic programming is essentially smarter recursion. It's about not repeating the same work.

These algorithms are best developed in two distinct stages.

(1) Formulate the problem recursively.

(a) Specification: What problem are you trying to solve?

(b) Solution: Why is the whole problem in terms of answers t smaller instances exactly the same problem?

(2) Find solutions to your recurrence from the bottom up

(a) Identify the subproblems

(b) Choose a memoization data structure

(c) Identify dependencies

(d) Find a good evaluation order

(e) Analyze space and running time

(f) Write down the algorithm

## Greedy Algorithms

If we're lucky we can just make decisions directly instead of solving any recursive subproblems. The problem is that greedly algorithms almost never work.