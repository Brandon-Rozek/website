---
title: "Expectations are Linear"
date: 2026-04-26T09:03:28-04:00
draft: false 
tags: []
math: true
medium_enabled: false
---

> As an example, he asked me, in more words, what the expected rank when flipping over the top card of a deck of cards was (A=1, J=11, Q=12,  K=13). This is easy to compute directly as 7. Then he asked me the expectation of the *sum of the top two cards*.
>
> \- [From "Expectation and Copysets" by Justin Jaffray](https://buttondown.com/jaffray/archive/expectation-and-copysets/)

What does your intuition say the answer is? Justin continues by stating that computing this expectation is as easy as summing their individual expectations.
$$
E[X + Y] = E[X] + E[Y]
$$
In other words, **expectations are linear**. I recommend reading his entire blog post. It's great and also talks about how this property is used in databases today. After a high-level explanation, he says: 

> The fact that expectation is linear is easy to show if you just look at the definition, which we will not do here, but I trust you are capable of if you are interested and have not already seen it.

In this episode of *Exercise for the Reader* ([last episode](/blog/implications-prenex-normal-form/)), we'll look at the definition and show why this property holds. This is true regardless of the underlying probability distribution and whether or not we're sampling with replacement.

As Justin stated, let's start with the definition of expectation and then split the sum:
$$
\begin{align*}
E[X + Y] &= \sum_{x \in X} \sum_{y \in Y} (x + y) \cdot P(X = x, Y=y) \\\\
&= (\sum_{x \in X} \sum_{y \in Y} x \cdot P(X = x, Y = y)) + (\sum_{x \in X} \sum_{y \in Y} y \cdot P(X = x, Y = y))
\end{align*}
$$
Notice that the left-hand-side of the multiplication does not depend on both variables anymore. Also it doesn't matter whether we do the summation over $X$ first or $Y$. Therefore, we can bring that variable out of the inner sum and simplify this to:
$$
E[X + Y] = (\sum_{x \in X} x \sum_{y \in Y} P(X = x, Y = y)) + (\sum_{y \in Y} y \sum_{x \in X} P(X = x, Y = y))
$$
We can then perform *marginalization* to substitute $\sum_{y \in Y} P(X = x, Y = y)$ with $P(X = x)$ and do the same for the right hand side of the sum.
$$
\begin{align*}
E[X + Y] &= (\sum_{x \in X}xP(X = x)) + (\sum_{y \in y}yP(Y=y))) \\\\
         &= E[x] + E[Y]
\end{align*}
$$

---

Why can we marginalize? For me to show why, we need to peel back the curtain on the notation.

The set $\Omega$ contains the outcomes of all the events that we're concerned about. So, if we are considering events $X$ and $Y$ with outcomes $x_i$ and $y_i$, respectively. Then, our event space $\Omega$ is equal to $\\{ (x_i, y_i) \mid x_i \in X, y_i \in Y\\}$.

Therefore when we say $X = x$, what we really mean is the set of outcomes where that is true. In mathematical terms, $\\{\omega \in \Omega \mid X(\omega) = x\\}$.

Now, let's show why $\sum_{y \in Y} P(X = x, Y = y) = P(X = x)$.
$$
\sum_{y \in Y}P(X = x, Y = y) = \sum_{y \in Y} P(\\{\omega \in \Omega \mid X(\omega) = x\\} \cap \\{\omega \in \Omega \mid Y(\omega) = y\\})
$$
One of the three Kolmogorov axioms of probability is **countable additivity**. This is defined as:
$$
\sum_{x \in A}P(X = x) = P(\bigcup_{x \in A}X =x )
$$
Substituting that in and simplifying, we get:
$$
\begin{align*}
\sum_{y \in Y}P(X = x, Y = y) &= P(\bigcup_{y \in Y}(\\{\omega \in \Omega \mid X(\omega) = x\\} \cap \\{\omega \in \Omega \mid Y(\omega) = y\\})) \\\\
&= P(\\{\omega \in \Omega \mid X(\omega) = x\\} \cap \bigcup_{y \in Y}\\{\omega \in \Omega \mid Y(\omega) = y\\})
\end{align*}
$$
Notice that the right hand side of the term is just $\Omega$. We can then simplify to,
$$
\begin{align*}
\sum_{y \in Y}P(X = x, Y = y) &= P(\\{\omega \in \Omega \mid X(\omega) = x\\} \cap \Omega) \\\\
&= P(\\{\omega \in \Omega \mid X(\omega) = x\\}) \\\\
&= P(X = x)
\end{align*}
$$
Since countable additivity is an axiom, we'll stop our derivations there.  See you next time.
