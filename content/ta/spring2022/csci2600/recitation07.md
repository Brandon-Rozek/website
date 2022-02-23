---
title: "PSoft Recitation 7: Exam Review"
date: 2022-02-22T21:28:34-04:00
draft: false
---

## Question 1: Forward Reasoning

Fill in the blanks using forward reasoning. Don't forget to:

- Carry your variables forward
- Show your work
- Simplify expressions
- State the strongest postcondition

```java
{x > 1}
y = x;
{                    }
x = x + 5;
{                    }
y = 2 * y;
{                    }
if (x < 12) {
    y = -x;
    {                        }
} else {
    y = -6 * y;
    {                        }
}
{                             }
```

## Question 2: Reasoning about loops

Consider the following Dafny code:

```csharp
method until_parity(y: int) returns (index: int)
    requires y < 0
    ensures index == (1 - y) / 2  || index == (-y / 2)
{
    var p := y;
    index := 0;
    while (p != 0 && p != 1)
        decreases -p
        invariant y <= p <= 1
        invariant index == (p - y) / 2
    {
        p := p + 2;
        index := index + 1;
    }
}
```

### Q2.1: Loop Invariants

Prove that `index == (p - y)  / 2` using induction

### Q2.2 Postcondition Verification

Show that the postcondition is provable from the loop invariant and loop condition.

### Q2.2 (Bonus) Decrementing Function

Prove that `-p` is the decrementing function.

## Question 3: Dafny Invariants

What is the missing invariant to make this code verify in Dafny?

```csharp
method copy(in_arr: array<int>) returns (out_arr: array<int>)
    ensures in_arr.Length == out_arr.Length
    ensures forall j :: 0 <= j < in_arr.Length ==> in_arr[j] == out_arr[j]
{
    out_arr := new int[in_arr.Length];
    var i := 0;
    while i < in_arr.Length
        invariant 0 <= i <= in_arr.Length
		// INVARIANT MISSING HERE
    {
        out_arr[i] := in_arr[i];
        i := i + 1;
    }
}
```

## Question 4: Backwards Reasoning

Fill in the blanks using forward reasoning. Don't forget to:

- Carry your variables forward
- Show your work
- Simplify expressions
- State the strongest precondition

```java
{                 }
w = 2 * w;
{                 }
z = -w;
{                 }
y = v + 1;
{                 }
x = min(y, z);
{      x < 0      }
```



## Question 5: Hoare Triple Validity

Assume the following are true:

```
{b} code {y}
a -> b
b -> c
x -> y
y -> z
```

For the following Hoare triples state whether or not they are valid.

If valid, why? If not valid, provide counterexample.

*Hint: Recall Liskov Principle of Substitutability*

**Q5.1:** Is `{a} code {y}` valid?

**Q5.2:** Is `{b} code {x}` valid?

**Q5.3:** Is `{b} code {z}` valid?