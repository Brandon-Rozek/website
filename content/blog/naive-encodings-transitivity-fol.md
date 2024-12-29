---
title: "Naive Encodings of Transitivity within First-Order Logic"
date: 2024-12-29T07:28:05-05:00
draft: false
tags: ["Logic"]
math: true
medium_enabled: false
---

> The transitive closure of a binary relation cannot, in general, be expressed in first-order logic (FO)

In Ray Reiter's book "Knowledge in Action: Logical Foundations for Specifying and Implementing Dynamical Systems", he goes over a typical naive encoding of transitivity in first-order logic and goes over a counter-example[^1].

[^1]: Unfortunately there was an errata in Example 2.1.1. The set `T` should be described as `{(b, a), (b, b)}` instead of the typo `{(a, b), (b, b)}`. Thanks James for noticing this!

Let $G$ be a binary relation that represents whether or not there is a direct edge between two nodes.

We want to axiomatize the transitive closure into the binary relation $T$. This means we need to have a formula that holds when we have a transitive closure, and does not hold when we do not.

A naive axiomatization is the following:
$$
T(x, y) \iff G(x, y) \vee \exists z(G(x, z) \wedge T(z, y))
$$
Ray's counter-example is the following. Consider the following valuation of $G$:

```
G: {(b, b)}
```

{{< unsafe >}}

<img height="300px" src="/files/images/blog/202412280944.svg"/>

<br/>

{{< /unsafe >}}

Now consider the following valuation of $T$:

```
T: {(b, a), (b, b)}
```

We falsely state that `b` is connected to `a` via transitive closure. If our axiomatization is sound, then it should be falsified.
$$
\begin{align*}
T(b, a) &\iff G(b, a) \vee \exists z (G(b, z) \wedge T(z, a))  \\\\
&\impliedby \bot \vee (G(b, b) \wedge T(b, a)) \\\\
&\impliedby \bot \vee (\top \wedge \top) \\\\
&\impliedby \top
\end{align*}
$$
However, the formula is satisfied! Therefore, this cannot be used to axiomatize transitive closure.

That's the end of the original counter-example in the book.  However, I thought it would be fun to extend the exercise.

The issue in the last example, is that we had a cycle in which we were able to define $T(b, a)$ in terms of $T(b, a)$. What if we add a constraint so that isn't the case?
$$
T(x, y) \iff G(x, y) \vee \exists z(z \ne x \wedge G(x, z) \wedge T(z, y))
$$
Does this new formula axiomatize transitive closure? The quote at the beginning begs to differ, so let's find a counter-example!

Consider the following valuations for $G$ and $T$:

```
G: {(b, a), (a, b)}
T: {(b, c), (a, c)}
```

{{< unsafe >}}

<img height="300px" src="/files/images/blog/202412281036.svg"/>

<br/>

{{< /unsafe >}}

As before, this model should not have transitive closure. Let's evaluate our modified formula.
$$
\begin{align*}
T(b, c) &\iff G(b, c) \vee \exists z (z \ne b \wedge G(b, z) \wedge T(z,c)) \\\\
&\impliedby \bot \vee (a \ne b \wedge G(b, a) \wedge T(a, c)) \\\\
&\impliedby \bot \vee (\top \wedge \top \wedge \top) \\\\
&\impliedby \top
\end{align*}
$$

$$
\begin{align*}
T(a, c) &\iff G(a, c) \vee \exists z (G(a, z) \wedge T(z, c)) \\\\
&\impliedby G(a, c) \vee (b \ne a \wedge G(a, b) \wedge T(b, c)) \\\\
&\impliedby \bot \vee (\top \wedge \top \wedge \top) \\\\
&\impliedby \top
\end{align*}
$$

Here we can see that the above valuations depending on each other. 

Wikipedia has a great [article](https://en.wikipedia.org/wiki/Transitive_closure) on transitive closure including a section on its use within logic and computational complexity.

> (First-order Transitive-Closure Logic) FO(TC) is strictly more expressive than FO.
