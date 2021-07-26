---
title: Recursion
showthedate: false
math: true
---

## Reductions

Quote: *Reduction* is the single most common technique used in designing algorithms. Reduce one problem $X$ to another problem $Y$. 

The running time of the algorithm can be affected by $Y$, but $Y$ does not affect the correctness of the algorithm. So it is often useful to not be concerned with the inner workings of $Y$.

## Simplify and Delegate

Quote: *Recursion* is a particularly powerful kind of reduction, which can be described loosely as follows:

- If the given instance of the problem can be solved directly, then do so.
- Otherwise, reduce it to one or more **simpler instances of the same problem.**

The book likes to call the delegation of simpler tasks "giving it to the recursion fairy."

Your own task as an algorithm writer is to simplify the original problem and solve base cases. The recursion fairy will handle the rest.

Tying this to mathematics, this is known as the **Induction Hypothesis**.

The only caveat is that simplifying the tasks must eventually lead to the **base case** otherwise the algorithm might run infinitely!

#### Example: Tower of Hanoi

Assuming you know how the game works, we will describe how to solve it.

Quote: We can't move it all at the beginning, because all the other disks are in the way. So first we have to move those $n - 1$ smaller disks to the spare peg. Once that's done we can move the largest disk directly to its destination. Finally to finish the puzzle, we have to move the $n -1$ disks from the spare peg to the destination.

**That's it.**

Since the problem was reduced to a base case and a $(n - 1)$ problem, we're good. The book has a funny quote "Our job is finished. If we didn't trust the junior monks, we wouldn't have hired them; let them do their job in peace."

 ```
Hanoi(n, src, dst, tmp):
  if n > 0
    Hanoi(n - 1, src, tmp, dst)
    move disk n from src to dst
    Hanoi(n - 1, tmp, dst, src)
 ```

## Sorting Algorithms

## Merge Sort

```
MergeSort(A[1..n]):
  if n > 1
    m = floor(n / 2)
    MergeSort(A[1..m])
    MergeSort(A[m + 1..n])
    Merge(A[1..n], m)
```

```
Merge(A[1..n], m):
  i = 1
  j = m + 1
  for k = 1 to n
    if j > n
      B[k] = A[i]
      i++
    else if i > m
      B[k] = A[j]
      j++
    else if A[i] < A[j]
      B[k] = A[i]
      i++
    else
      B[k] = A[j]
      j++
  Copy B to A
```

I think an important part to recall here is that the algorithm will break it down to the lowest level. An array with one element and slowly work its way up.

That means we can always assume that each subarray that we're merging is already sorted! Which is why the merge algorithm is written the way it is.

## The Pattern

This section is quoted verbatim.

1. **Divide** the given instance of the problem into several *independent smaller* instances of *exactly* the same problem.
2. **Delegate** each smaller instance to the Recursion Fairy.
3. **Combine** the solutions for the smaller instances into the final solution for the given instance.

