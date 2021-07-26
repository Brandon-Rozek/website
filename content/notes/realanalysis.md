---
title: Real Analysis Quick Sheet
showthedate: false
math: true
---

**Fact:** $\forall a,b, \in \mathbb{R}$, $\sqrt{ab} \le \frac{1}{2}(a + b)$.

**Bernoulli's Inequality:** If $x > -1$, then $(1 + x)^n \ge 1 + nx$, $\forall n \in \mathbb{N}$.

**Triangle Inequality:** If $a,b \in \mathbb{R}$, then $|a + b| \le |a| + |b|$.

**Epsilon Neighborhood Definition:**

Let $a \in \mathbb{R}$ and $\epsilon > 0$. The $\epsilon$-neighborhood of $a$ is the set $V_\epsilon(a) = \{ x \in \mathbb{R}, |x - a| < \epsilon\}$.

**Archimedean Property:** If $x \in \mathbb{R}$, then $\exists n_x \in \mathbb{N}$ such that $x \le n_x$.

**Convergence Definition:**

$X = (x_n)$ converges to $x \in \mathbb{R}$ if $\forall \epsilon > 0, \exists k \in \mathbb{N}$ such that $\forall n \ge k, |x_n - x| < \epsilon$.

**Fact:** A sequence in $\mathbb{R}$ can have at most one limit.

**Theorem 3.1.9:**

If $(a_n)$ is a sequence in $\mathbb{R}$ such that $a_n \rightarrow 0$, and for some constant $c > 0, m \in \mathbb{N}$,

$|x_n - x| \le ca_n, \forall n \ge m$, then $x_n \rightarrow x$.

**Theorem 3.2.7:**

(a) If $x_n \rightarrow x$, then $|x_n| \rightarrow |x|$.

(b) If $x_n \rightarrow x$ and $x_n \ge 0$, then $\sqrt{x_n} \rightarrow \sqrt{x}$.

**Ratio Test:**

Let $\{x_n\} \subseteq \mathbb{R}^+$ such that $L = \lim{(\frac{x_{n + 1}}{x_n})}$. If $L < 1$, then $x_n \rightarrow 0$.

**Theorem 3.2.2:** Every convergent sequence is bounded. (The converse is not necessarily true)

**Squeeze Theorem:**

If $x_n \rightarrow x, y_n \rightarrow y,$ and $z_n \rightarrow x$ such that $x_n \le y_n \le z_n, \forall n \in \mathbb{N}$ then $y = x$.

**Monotone Convergence Theorem**

Let $X = (x_n)$ be a subsequence in $\mathbb{R}$.

(a) If $X$ is monotonically increasing and bounded above then $\lim{x_n} = sup\{x_n : n \in \mathbb{N}\}$

(b) If $X$ is monotonically decreasing and bounded below then $\lim{x_n} = inf\{x_n : n \in \mathbb{N}\}$

**Useful Fact:** If $\lim{x_n} = a \in \mathbb{R}$, then $\lim{x_{n + 1}} = a$.

**Interesting Application of MCT:** 

Let $s_1 > 0$ be arbitrary, and define $s_{n + 1} = \frac{1}{2}(s_n + \frac{a}{s_n})$. We know $s_n \rightarrow \sqrt{a}$.

**Euler's Number:** Consider the sequence $e_n = (1 + \frac{1}{n})^n$. We know $e_n \rightarrow e$.

**Theorem 3.4.2:** If $X = (x_n) \subseteq \mathbb{R}$ converges to $x$, then every subsequence converges to $x$.

**Corollary:** If $X = (x_n) \subseteq \mathbb{R}$ has a subsequence that diverges then $X$ diverges.

**Monotone Sequence Theorem**: If $X = (x_n) \subseteq \mathbb{R}$, then it contains a <u>monotone subsequence</u>.

**Bolzano-Weierstrass Theorem:** Every bounded sequence in $\mathbb{R}$ has a convergent subsequence.

**Theorem 3.4.12:** A bounded $(x_n) \in \mathbb{R}$ is convergent iff $liminf(x_n) = limsup(x_n)$.

**Cauchy Criteria for Convergence:** Let $X = (x_n) \subseteq \mathbb{R}$. We say that $X$ is cauchy if $\forall \epsilon > 0, \exists N \in \mathbb{N}$ such that $\forall n,m \ge N, |x_n - x_m| < \epsilon$. We know that a sequence converges iff it is cauchy.

**P-Series:** Series of the form $s_n = \sum_{i = 0}^n{\frac{1}{n^p}}$ is convergent for $p > 1$.

**Geometric Series:** 

Series of the form $s_n = \sum_{i = 0}^n{ar^i}$ has the following partial sum $a\frac{1 - r^n}{1 - r}$ and converges to $\frac{a}{1 - r}$ if $|r| < 1$.

**Comparison Test:**

Let $(x_n), (y_n) \subseteq \mathbb{R}$. Suppose that for some $k \in \mathbb{N}, 0 \le x_n \le y_n,$ for $n \ge k$.

(a) If $\sum{y_n} < \infty$, then $\sum{x_n} < \infty$.

(b) If $\sum{x_n} = \infty$, then $\sum{y_n} = \infty$.

**Limit Comparison Test:**

Let $(x_n), (y_n)$ be strictly positive sequence of real numbers. Suppose $r = \lim{\frac{x_n}{y_n}}$.

(a) If $r \ne 0$, then $\sum{x_n} < \infty \iff \sum{y_n} < \infty$.

(b) If ($r = 0$ and $\sum{y_n} < \infty$), then $\sum{x_n} < \infty$.

 
