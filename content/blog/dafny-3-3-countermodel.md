---
date: 2022-02-04 19:43:12-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: b1976dcfde09
tags:
- Formal Methods
title: Dafny v3.3 Show Countermodel
---

*Warning: `extractcounterexample` is a new flag in Dafny and the command to extract it will likely change*

[Dafny](https://www.microsoft.com/en-us/research/project/dafny-a-language-and-program-verifier-for-functional-correctness/) is a program verifier made by Microsoft. The programmer specifies the pre and post conditions and Dafny will try to verify that the codebase meets those specifications. One of its coolest features is that Dafny will can provide a countermodel for why it things the code does not verify.  Lets look at an example:	

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
        invariant forall j, k :: 0 <= j <= k < i ==> a[j] <= a[k]
    {
        a[i] := i;
        i := i + 1;
    }
}
```

Say the content above is saved in  `example.dfy`. To verify it and show a countermodel if it fails:

```bash
dafny example.dfy \
	/compile:4 /verifyAllModules \
	/proverOpt:O:model_compress=false \
	/proverOpt:O:model.completion=true \
	/warnShadowing /extractCounterexample \
	/errorTrace:0 /mv:example.model
```

The output can be a bit cryptic:

```
example.dfy(14,18): Error: This loop invariant might not be maintained by the loop.
example.dfy(14,18): Related message: loop invariant violation

Dafny program verifier finished with 1 verified, 1 error
Compiled assembly into example.dll
Program compiled successfully
Counterexample for first failing assertion: 
example.dfy(7,0): initial state:
        a : _System.array?<int> = ()
        n : int = 1237
        j : int = 196
        k : int = 1236
example.dfy(8,14):
        a : _System.array?<int> = ()
        n : int = 1237
        i : int = 0
        j : int = 196
        k : int = 1236
example.dfy(9,19):
        a : _System.array?<int> = (Length := 1237, [1236] := 1236, [196] := 1686)
        n : int = 1237
        i : int = 0
        j : int = 196
        k : int = 1236
example.dfy(10,4): after some loop iterations:
        a : _System.array?<int> = (Length := 1237, [196] := 1686)
        n : int = 1237
        i : int = k
        j : int = 196
        k : int = 1236
example.dfy(16,17):
        a : _System.array?<int> = (Length := 1237, [1236] := 1236, [196] := 1686)
        n : int = 1237
        i : int = k
        j : int = 196
        k : int = 1236
example.dfy(17,18):
        a : _System.array?<int> = (Length := 1237, [1236] := 1236, [196] := 1686)
        n : int = 1237
        i : int = n
        j : int = 196
        k : int = 1236

```

The important thing to note here is that it thinks `a[196] = 1686` which is not true at all given the code. Turns out, we'll have to add an extra loop invariant in order for it to verify correctly:

```csharp
invariant forall k :: 0 <= k < i ==> a[k] == k
```

Running Dafny again will produce:

```
Dafny program verifier finished with 2 verified, 0 errors
Compiled assembly into example3.dll
Program compiled successfully
```