---
title: "Program Verification with Hoare Logic and Dafny"
date: 2022-02-05T00:06:42-05:00
draft: false
tags: ["Formal Methods"]
math: false
---

In the recitations that I'm giving for [Principles of Software](https://brandonrozek.com/ta/spring2022/csci2600/), we are going over reasoning through code using Hoare Logic and the program verifier Dafny. Microsoft Research designed Dafny to be similar to writing imperative code. The main difference is that you need to supply (pre/post)-conditions and the code to verify. Here's an example of how to reason about a simple statement by hand:

```csharp
// Precondition: x > 0
x := x + 1;
// Postcondition: x > 1
```

Given the fact that x is greater than zero before the code begins, we can deduce that if we increment it by one then it must be greater than one! Though to showcase Dafny, we'll look at a slightly more interesting (albeit famous beginner example) which is the absolute value:

```csharp
method abs(x: int) returns (y: int)
    requires true
    ensures y >= 0
    ensures x >= 0 ==> x == y
{
    if (x < 0) {
        y := -x;
    } else {
        y := x;
    }
}
```

The `requires` clause is otherwise known as the precondition or what is known to be true before the method executes. For the case of absolute value, we do not need to constrain any of the integer inputs, so we can put `requires true` or not even include that line.

The `ensures` clause is otherwise known as the postcondition or what you want verified to be true after the method executes. In there we have two conditions: the output must be positive, and if the input was positive then the output equals the input.

Then finally the code goes in the method body.

Now you can actually verify it line by line through the use of `assert` statements. Here's the same method again but with assertions:

```csharp
method abs(x: int) returns (y: int)
    requires true
    ensures y >= 0;
    ensures x >= 0 ==> x == y
{
    if (x < 0) {
        assert x < 0;
        y := -x;
        assert y > x;
    } else {
        assert x >= 0;
        y := x;
        assert y == x;
    }
}
```





