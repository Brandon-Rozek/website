---
title: Handy Facts about Quadratic Congruences
showthedate: false
math: true
---

## Number of Solutions

*For congruences mod 2*

**Proposition 16.1**. Let $f(x) = ax^2 + bx + c$ with $a$ odd, and let $\Delta = b^2 - 4ac$ be the discriminant of $f(x)$. Then,

1. If $\Delta \equiv 1$ (mod $8$), so that $b$ is odd and $c$ is even, then $f(x) \equiv 0$ (mod $2$) has **two** solutions
2. If $\Delta \equiv 5$ (mod $8$), so that $b$ and $c$ are odd, then $f(x) \equiv 0$ (mod $2$) has **no** solutions
3. If $4 | \Delta$ ,  so that $b$ is even, then $f(x) \equiv 0$ (mod $2$) has exactly **one** solution.

**Proposition 16.2.** Let $p$ be an odd prime and let $a$ be an integer. Then,

1. If $p$ does not divide $a$, then the congruence $x^2 \equiv a$ (mod $p$) has either two solutions or no solutions. 
2. If $p$ divides $a$, then $x^2 \equiv a$ (mod $p$) has exactly one solution, namely $x = 0$.

**Legendre symbol definition**. Let $p$ be an odd prime and $a$ any integer. Then the *Legendre symbol*, written as $(\frac{a}{p})$ is defined as
$$
(\frac{a}{p}) = \begin{cases}
1, & \text{if $x^2 \equiv a$ (mod $p$) has exactly two solutions,} \\
0, & \text{if $x^2 \equiv a$ (mod $p$) has exactly one solution,} \\
-1, & \text{if $x^2 \equiv a$ (mod $p$) has no soultions.}
\end{cases}
$$
**Properties of Legendre symbol**.

- $(\frac{a}{p}) = 0 \iff p$ divides $a$

- $(\frac{1}{p}) = 1$ for every odd prime $p$

- $a \equiv b$ (mod $p$) $\implies$ $(\frac{a}{p}) = (\frac{b}{p})$

- $(\frac{ab}{p}) = (\frac{a}{p})(\frac{b}{p})$

- If $p$ is an odd prime then,

  - $$
    (\frac{-1}{p}) = 
    \begin{cases} 
    1, & \text{if $p \equiv 1$ (mod $4$)} \\
    -1, & \text{ if $p \equiv 3$ (mod $4$)}
    \end{cases}
    $$

- If $p$ is an odd prime then,

  - $$
    (\frac{2}{p}) = 
    \begin{cases} 
    1, & \text{if $p \equiv 1$ (mod $8$) or $p \equiv 7$ (mod $8$)} \\
    -1, & \text{ if $p \equiv 3$ (mod $8$) or $p \equiv 5$ (mod $8$)}
    \end{cases}
    $$

- **Quadratic Reciprocity Theorem**. Let $p$ and $q$ be distinct odd primes. Then,

  - $$
    (\frac{q}{p}) = 
    \begin{cases} 
    (\frac{p}{q}), & \text{if $p \equiv 1$ (mod $4$) or $q \equiv 1$ (mod $4$)} \\
    -(\frac{p}{q}), & \text{ if $p \equiv 3$ (mod $4$) and $q \equiv 3$ (mod $4$)}
    \end{cases}
    $$

## Procedure

When $p$ is an odd prime, a quadratic congruence $ax^2 + bx + c \equiv 0$ (mod $p$) can be transformed into a specialized form by completing the square.
\begin{align*}
ax^2 + bx + c \equiv 0 \text{ (mod $p$)} &\iff 4a(ax^2 + bx + c) \equiv 0 \text{ (mod $p$)} \\\\
&\iff 4a^2x^2 + 4abx + 4ac \equiv 0 \text{ (mod $p$)} \\\\
&\iff 4a^2x^2 + 4abx + 4ac + (b^2 - 4ac) \equiv b^2 - 4ac  \text{ (mod $p$)} \\\\
&\iff 4a^2x^2 + 4abx + b^2 \equiv b^2 - 4ac \text{ (mod $p$)} \\\\
&\iff (2ax+b)^2 \equiv b^2 - 4ac \text{ (mod $p$)}
\end{align*}

## Quadratic Congruences Modulo a prime power

Let $a$ be the solution to $f(x) \equiv 0$ (mod $p$) where $p$ is an odd prime. Consider $b = pt + a$. Then, $f(b) \equiv 0$ (mod $p^2$) if $f^\prime(a)t \equiv -\frac{f(a)}{p}$ (mod $p$).

In general, let $a$ be the solution to $f(x) \equiv 0$ (mod $p^n$) where $p$ is an odd prime. Consider $b = pt + a$. Then, $f(b) \equiv 0$ (mod $p^{n + 1}$) if $f^\prime(a)t \equiv -\frac{f(a)}{p^n}$ (mod $p$) 

