---
title: "Groups in Abstract Algebra"
draft: false
tags: []
math: true
---

Let us have a set $G$ together with some binary operation $*$.
We will use multipicative notation where $ab = a * b$.
Let $x, y, z \in G$. If $\langle G, *\rangle$ has the
following properties:
1. $(xy)z = x(yz)$
2. $ex = x$
3. $x^{-1}x = e$

for some fixed $e \in G$, then we say that $\langle G, *\rangle$ is a group.
In my class, we were also told to show that $xe = x$ and $xx^{-1} = e$.
However, these can be derived by the prior three properties.

## Prove $xx^{-1} = e$

$$
\begin{align*}
e &= (xx^{-1})^{-1}(xx^{-1}) \\\\
  &= (xx^{-1})^{-1}(x(ex^{-1})) \\\\
  &= (xx^{-1})^{-1}(x((x^{-1}x)x^{-1})) \\\\
  &= (xx^{-1})^{-1}(x(x^{-1}x)x^{-1}) \\\\
  &= (xx^{-1})^{-1}((xx^{-1})(xx^{-1})) \\\\
  &= ((xx^{-1})^{-1}(xx^{-1}))(xx^{-1}) \\\\
  &= e(xx^{-1}) \\\\
  &= xx^{-1} \\\\
\end{align*}
$$

## Prove $xe = x$

We can use the last proof to solve this faster.

$$
\begin{align*}
x &= ex \\\\
  &= (xx^{-1})x \\\\
  &= x(x^{-1}x) \\\\
  &= xe
\end{align*}
$$
