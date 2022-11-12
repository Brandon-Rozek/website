---
title: "Reasoning through Loops in Dafny"
date: 2022-02-05T00:22:58-05:00
draft: false
tags: ["Formal Methods"]
math: true
---

Dafny treats loops like a black box. It could be annoying the first time you experience this and have no clue why the code is not verifying properly. There are two properties that Dafny needs you to prove: partial correctness and termination. Together these form *total correctness*.

## Partial Correctness

Partial correctness is concerned with whether the system is sound and complete. In other words, if the loop terminates that the postcondition holds for all possible inputs constrained by the precondition.

```csharp
method arrayUpToN(n: int) returns (a: array<int>)
    requires n >= 0
    ensures a.Length == n
    ensures forall j :: 0 < j < n ==> a[j] >= 0
    ensures forall j, k : int :: 0 <= j <= k < n ==> a[j] <= a[k]
{
    var i := 0;
    a := new int[n];
    while i < n
    {
        a[i] := i;
        i := i + 1;
    }
}
```

In order to solve this, we need to concept of a loop invariant. A loop invariant is a formula that is true before, during, and after the loop. In order to prove the postcondition, we need to choose the relevant loop invariants such that:
$$
\neg Loop\_Condition \wedge Loop\_Invariants \implies Post\_Condition
$$
If this is not the case, then Dafny will likely complain to you as it has no clue what's going on. I generally always first add bounds to the iterator and other variables.

```csharp
invariant 0 <= i <= n
```

Here are the other invariants you'll need in order for the postcondition in the example to verify:

```csharp
invariant forall k :: 0 <= k < i ==> a[k] >= 0
invariant forall k :: 0 <= k < i ==> a[k] == k
invariant forall j, k :: 0 <= j <= k < i ==> a[j] <= a[k]
```

Together this forms:

```csharp
method arrayUpToN(n: int) returns (a: array<int>)
    requires n >= 0
    ensures a.Length == n
    ensures forall j :: 0 < j < n ==> a[j] >= 0
    ensures forall j, k : int :: 0 <= j <= k < n ==> a[j] <= a[k]
{
    var i := 0;
    a := new int[n];
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> a[k] >= 0
        invariant forall k :: 0 <= k < i ==> a[k] == k
        invariant forall j, k :: 0 <= j <= k < i ==> a[j] <= a[k]
    {
        a[i] := i;
        i := i + 1;
    }
}
```

## Termination

Termination is concerned with whether your loop will finish in finite time. The way that Dafny does this is by guessing what is called the Decrementing function. In Dafny, the decrementing function is required to:

- Decrease with each iteration of the loop
- Be bounded below by zero

In the last example, Dafny was able to correctly guess that decrementing function was $n - i$. What about the following example:

```csharp
method fact(x: int) returns (y: int)
    requires x >= 0
{
    var z := 0;
    y := 1;
    while z != x
        invariant 0 <= z <= x
    {
        z := z + 1;
        y := y * z;
    }
}
```

Turns out in this scenario, Dafny was not able to successfully guess. To supply it with the decrementing function use the keyword `decreases`.

```csharp
method fact(x: int) returns (y: int)
    requires x >= 0
{
    var z := 0;
    y := 1;
    while z != x
        decreases x - z
        invariant 0 <= z <= x
    {
        z := z + 1;
        y := y * z;
    }
}
```



