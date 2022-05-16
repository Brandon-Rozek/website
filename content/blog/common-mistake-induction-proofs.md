---
title: "Most Common Mistake in Induction Proofs"
date: 2022-05-15T22:49:34-04:00
draft: false
tags: []
math: true
---

One of the most common mistakes I see in induction proofs is assuming the recursive case and working backwards towards the induction hypothesis. This may be fine for formulas that are symmetric like those involving equality, but this way of proving induction fails if not. This post will show such example.

## Question

Prove $x - 1 \ge \frac{x}{2}$ for $x \in \mathbb{Z}^+$

## Base Case

Let $x = 1$. Then,
$$
\begin{align*}
1 -1 &\ge \frac{1}{2} \\\\
0 &\ge 0 \checkmark
\end{align*}
$$
The right side simplifies to zero since we're doing integer division.

## Recursive Case (Correct)

Let us assume the induction hypothesis, that is, $x_n - 1 \ge \frac{x_n}{2}$. We will show that $x_{n + 1} - 1 \ge \frac{x_{n + 1}}{2}$. 

We know $x_{n + 1} = x_n + 1$, therefore, $x_n = x_{n + 1} - 1$.

Substituting into our inductive hypothesis:
$$
\begin{align*}
(x_{n + 1} - 1) - 1 &\ge \frac{x_{n + 1} - 1}{2} \iff \\\\
(x_{n + 1} - 1) - 1 &\ge \frac{x_{n + 1}}{2} - \frac{1}{2} \iff \\\\
x_{n + 1} - 1 &\ge \frac{x_{n + 1}}{2} + \frac{1}{2} \implies \\\\
x_{n + 1} - 1 &\ge \frac{x_{n + 1}}{2}
\end{align*}
$$
Therefore, via induction this theorem holds. Note that the last step was only an implication, this is where the symmetry breaks. 

## Recursive Case (Incorrect)

Now let us see how we can go astray if we start from the wrong direction. Substituting what we know about $x_n$ and $x_{n + 1}$:
$$
\begin{align*}
x_{n + 1} - 1 &\ge \frac{x_{n + 1}}{2} \iff \\\\
(x_n + 1) - 1 &\ge \frac{(x_n + 1)}{2} \iff \\\\
x_n &\ge \frac{x_n}{2} + \frac{1}{2} \iff \\\\
x_n -1 &\ge \frac{x_n}{2} - \frac{1}{2} 
\end{align*}
$$
Sadly from here we cannot imply that $x_n - 1 \ge \frac{x_n}{2}$.

## Conclusion

Remember, when performing the induction step of the proof:

- State the induction hypotheses
- State what formulas you know about the various variables
- Substitute into the **induction hypothesis**
- Simplify until you reach the $n+1$th step.

