---
date: 2022-02-26 19:17:21-05:00
draft: false
math: true
medium_enabled: true
medium_post_id: 395dbef73491
tags:
- Formal Methods
title: Loop Invariants
---

Loop invariants are one of the more complicated concepts in Hoare Logic. One might say that we can simply unroll the loop, but there are many loops where we don't know the number of iterations in advanced. Therefore, we often consider what is called the loop invariant. These are statements that are true before, during, and after the loop. A useful loop invariant in combination of the negation of the loop condition can also prove some postcondition. Lets look at a multiplication example

```java
int mul(int a, int b) {
    int x = 0;
    int p = 0;
    while (p < b) {
        x = x + a;
        p = p + 1;
    }
}
```

## Choosing the Loop Invariant

A useful postcondition in this case would be `x == a * b`. Which loop invariant would help us prove this? Often when crafting loop invariants I have two pieces of advice:

- The loop invariant should involve some part of the postcondition
- The loop invariant should involve the iterator

For the example above, the loop invariant should be `x == a * p`.

If you are using a verifier like Dafny, there are [additional invariants](/blog/dafny-loops/) you'll likely need to add.

## Proving the Loop Invariant

Often we'll use induction to prove the loop invariant. As a reminder induction has four steps:

1. Show the base case holds.
2. State the induction hypothesis.
3. State the propositions from the code.
4. Substitute (3) into (2) until the inductive step is proved. 

Below is a proof for the loop invariant `x == a * p` using induction.

Consider the base case `x = 0; p = 0`
$$
\begin{align*}
x &== a * 0 \\\\
0 &== 0 \checkmark
\end{align*}
$$
Let us assume the inductive hypothesis holds. That is, `x_n = a * p_n`. Notice that `a` does not change during the loop so there is no need to add a subscript to it.

Now we need to know what `x_n` and `p_n` are at any point during the loop. Looking at the code we come up with the following two propositions:
$$
p_{n + 1} == p_n + 1 \\\\
x_{n + 1} == x_n + a
$$
Then solving for the nth iteration:
$$
p_n == p_{n + 1} - 1 \\\\
x_n == x_{n + 1} - a
$$
We can then plug that into our inductive hypothesis and simplify.
$$
\begin{align*}
x_n &== a * p_n \\\\
x_{n + 1} - a &== a * (p_{n + 1} - 1) \\\\
x_{n + 1} - a &== a * p_{n + 1} - a \\\\
x_{n + 1} &== a * p_{n + 1} \checkmark
\end{align*}
$$
With that we've proved using induction that our loop invariant holds.

## Proving the Postcondition

To show that a postcondition holds, we need to show that the loop invariant and the negation of the loop condition imply the postcondition.
$$
(x_n == a * p_n) \wedge \neg(p < b) \implies_? x == a * b
$$
Simplifying...
$$
(x_n == a * p_n) \wedge \neg(p < b) \\\\
\implies (x_n == a * p_n) \wedge (p \ge b) \\\\
\implies (x_n \ge a * b)
$$
We need another loop invariant to show us that $p$ would never be greater than $b$. That is $0 \le p \le b$. That gives us:
$$
(x_n == a * p_n) \wedge (p \ge b) \wedge (p \le b) \\\\
 \implies (x_n == a * p_n) \wedge (p == b) \\\\
 \implies (x_n == a * b) \checkmark \\
$$