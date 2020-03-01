---
title: "Groups Simplified"
date: 2019-12-10T21:40:00-05:00
draft: false 
tags: [ "abstract algebra" ]
---

This post is inspired by the book "Term Rewriting & All That" by Franz Baader and Tobias Nipkow.

Let us have a set $G$ together with a binary operation $*$. We will use multiplicative notation throughout meaning $ab = a * b$. Let $x, y, z \in G$. If $\langle G , * \rangle$ has the following properties: 

1. $(x y)z = x (y z)$
2. $ex = x$ 
3. $x^{-1} x = e$

for some fixed $e \in G$, then we say that $\langle G, * \rangle$ is a group. In class, we needed to show that $xe = x$ and $xx^{-1} = e$. However, these can be derived by the prior properties.

### Prove $xx^{-1} = e$  
\begin{align*}
e &= (xx^{-1})^{-1}(x x^{-1}) \\\\
&= (xx^{-1})^{-1} (x (ex^{-1})) \\\\
&= (xx^{-1})^{-1} (x ((x^{-1} x) x^{-1})) \text{ ----- (A)} \\\\
&= (x x^{-1})^{-1} (x (x^{-1} x)x^{-1}) \\\\
&= (x x^{-1})^{-1}((x x^{-1})xx^{-1}) \\\\
&= (x x^{-1})^{-1} ((xx^{-1}) (x x^{-1})) \\\\
&= ((x x^{-1})^{-1}(x  x^{-1})) (x x^{-1}) \\\\
&= e(xx^{-1}) \\\\
&= xx^{-1}
\end{align*}
### Prove $xe = x$ 

Once we showed $xx^{-1} = e$, the proof of $xe = e$ is simple.
\begin{align*}
x &= ex \\\\
&= (xx^{-1})x \\\\
&= x(x^{-1}x) \\\\
&= xe
\end{align*}
