---
title: Number Theory for ACM ICPC
math: true
---

## Prime Numbers

A *prime number* is an integer $p > 1$ which is only divisible by $1$ and itself. 

If $p$ is a prime number, then $p = ab$ for integers $a \le b$ implies that $a = 1$ and $b = p$.

### Definitions

**Fundamental Theorem of Arithmetic**: Every integer can be expressed in only one way as a product of primes. 

**Prime factorization of $n$**: The unique set of numbers multiplying to $n$.

**Factor**: A prime number $p$ is a *factor* of $x$ if it appears in its prime factorization.

**Composite**: A number which is not prime

### Finding Primes

The easiest way to test if a given number $x$ is repeated division

- After testing two, we only need to check odd numbers afterwards
- We only need to check until $\sqrt{x}$ since two numbers are perhaps multiplied to achieve $x$.

#### Considerations if you don't have nice things

The terminating condition of $i > \sqrt{x}$ is somewhat problematic, because `sqrt()` is a numerical function with imperfect precision.

To get around this, you can change the termination condition to $i^2 > x$. Though then we get into the problem of potential overflow when working on large integers.

The best solution if you have to deal with these issues is to compute $(i + 1)^2$ based on the result from $i^2$.
$$
\begin{align*}
(i + 1)^2 &= i^2 + 2i + 1
\end{align*}
$$
So just add $(2i + 1)$ to the previous result.

## Divisibility

A lot of number theory concerns itself with the study of integer divisibility.

### Definition

**Divides:** We say that $b$ *divides* $a$ (denoted $b|a$) if $a = bk$ for some integer $k$.

**Divisor:** If the above is true, then we say that $b$ is a *divisor* of $a$

**Multiple:** Given the above, we say that $a$ is a multiple of $b$.

As a consequence of this definition, the smallest natural divisor of every non-zero integer is $1$. This is also known as the *least common divisor*.

**Greatest Common Divisor $(gcd)$:** the *largest* divisor shared by a given pair of integers.

**Relatively Prime**: Two integers are *relatively prime* if their greatest common divisor is $1$.

**Reduced Form:** A fraction is said to be in *reduced form* if the greatest common divisor between the numerator and denominator is $1$.

### Properties

The greatest common divisor an integer has with itself is itself.
$$
gcd(b, b) = b \tag{1.1}
$$
The ordering of arguments to $gcd$ doesn't matter. Traditionally the larger value is placed in the first argument.
$$
gcd(a, b) = gcd(b, a) \tag{1.2}
$$
The greatest common divisor if $b$ divides $a$ between $a$ and $b$ is $b$.
$$
b | a \implies gcd(a, b) = b \tag{1.3}
$$

This in part is because of two observations

- $b$ is the greatest common divisor of $b$ from $(1.1)$
- $b$ divides $a$, therefore it's a common divisor

The greatest common divisor between $a$ and $b$ where $a = bt + r$ is the same as the greatest common divisor between $b$ and $r$.
$$
a = bt + r \implies gcd(a, b) = gcd(b, r) \tag{1.4}
$$
Let's work this out: $gcd(a, b) = gcd(bt + r, b)$. Since $bt$ is a multiple of $b$, we can add and subtract as many $bt$'s as we want without influencing the answer. This leads to $gcd(bt + r, b) = gcd(r, b) = gcd(b, r)$.

### Euclid's Algorithm

Using $(1.4)$ we can rewrite greatest common divisor problems in terms of the property in order to simplify the expression. Take a look at the example below:
$$
\begin{align*}
gcd(34398, 2131) &= gcd(34398 \text{ mod } 2132, 2132) = gcd(2132, 286) \\
gcd(2132, 286) &= gcd(2132 \text{ mod } 286, 286,) = gcd(286, 130) \\
gcd(286, 130) &= gcd(286 \text{ mod } 130, 130) = gcd(130, 26) \\
gcd(130, 26) &= gcd(130 \text{ mod } 26, 26,) = gcd(26, 0)
\end{align*}
$$
Therefore, $gcd(34398, 2132) = 26$.

### Least Common Multiple

#### Definition

The *least common multiple* $(lcm)$ is the smallest integer which is divided by both of a given pair of integers. Ex: $lcm(24, 36) = 72$.

#### Properties

The least common multiple of $x$ and $y$ is greater (or equal) than both $x$ and $y$.
$$
lcm(x, y) \ge max(x,y) \tag{2.1}
$$
The least common multiple of $x$ and $y$ is less than or equal to $x$ and $y$ multiplied together.
$$
lcm(x, y) \le xy \tag{2.2}
$$
Coupled with Euclid's algorithm we can derive the property that the least common multiple is equal to the pair of multiplied integers divided by their greatest common divisor.
$$
lcm(x, y) = xy / gcd(x, y) \tag{2.3}
$$

#### Potential Problems

Least common multiple arises when we want to compute the simultaneous periodicity of two distinct periodic events. When is the next year (after 2000) that the presidential election will coincide with the census? 

These events coincide every twenty years, because $lcm(4, 10) = 20$. 

## Modular Arithmetic

We are not always interested in full answers, however. Sometimes the remainder suffices for our purposes.

<u>Example:</u> Suppose your birthday this year falls on a Wednesday. What day of the week will it fall on next year?

The remainder of the number of days between now and then (365 or 366) mod the number of days in a week. $365$ mod $7 = 1$. Which means that your birthday will fall on a Thursday.

### Operations of Modular Arithmetic

**Addition**: $(x + y)$ mod $n$ $=$ $((x $ mod $n) + (y$ mod $n))$ mod $n$

<u>Example:</u> How much small change will I have if given \$123.45 by my mother and \$94.67 by my father?
$$
\begin{align*}
(12345 \text{ mod } 100) + (9467 \text{ mod } 100) &= (45 + 67) \text{ mod } 100 \\
&= 12 \text{ mod } 100
\end{align*}
$$
**Subtraction** (Essentially addition with negatives):

<u>Example:</u> Based on the previous example, how much small change will I have after spending \$52.53?
$$
(12 \text{ mod } 100) - (53 \text{ mod } 100) = -41 \text{ mod } 100 = 59 \text{ mod } 100
$$
Notice the flip in signs, this can be generalized into the following form:
$$
x \text{ mod } y = (y - x) \text{ mod } y
$$
**Multiplication** (Otherwise known as repeated addition):
$$
xy \text{ mod } n  = (x \text{ mod } n)(y \text{ mod } n) \text{ mod n}
$$
<u>Example:</u> How much change will you have if you earn \$17.28 per hour for 2,143 hours?
$$
\begin{align*}
(1728 * 2143) \text{ mod } 100 &= (28 \text{ mod } 100)(43 \text{ mod 100}) \\
&= 4 \text{ mod } 100
\end{align*}
$$
**Exponentiation** (Otherwise known as repeated multiplication):
$$
x^y \text{ mod } n =(x \text{ mod n})^y \text{ mod } n
$$
<u>Example:</u> What is the last digit of $2^{100}$?
$$
\begin{align*}
2^3 \text{ mod } 10 &= 8 \\
2^6 \text{ mod } 10 &= 8(8) \text{ mod } 10 \rightarrow 4 \\
2^{12} \text{ mod } 10 &= 4(4) \text{ mod } 10 \rightarrow 6 \\
2^{24} \text{ mod } 10 &= 6(6) \text{ mod } 10 \rightarrow 6 \\
2^{48} \text{ mod } 10 &= 6(6) \text{ mod } 10 \rightarrow 6 \\
2^{96} \text{ mod } 10 &= 6(6) \text{ mod } 10 \rightarrow 6\\
2^{100} \text{ mod } 10 &= 2^{96}(2^3)(2^1) \text{ mod } 10 \\
						&= 6(8)(2) \text{ mod } 10 \rightarrow 6
\end{align*}
$$

## Linear Congruences

**Definition:** $ a \equiv b \text{ (mod m)} \iff m |(a-b)$

### Properties

If $a$ mod $m$ is $b$, then $a$ is linearly congruent to $b$ in mod $m$.
$$
a \text{ mod } m = b \implies a \equiv b \text{ (mod m)} \tag{3.1}
$$
Let us show that from what we know so far...
$$
\begin{align*}
a \text{ mod m} = b &\implies a = mk+b \hspace{.2in} \text{(for some $k \in \mathbb{Z}$)} \\
&\implies a - b = mk + b - b \\
&\iff a-b = m k \\
&\iff m | (a - b) \\
&\iff a \equiv b \hspace{.2in} \text{ (mod m)}
\end{align*}
$$
**Example:** What set of integers satisfy the following congruence?
$$
x \equiv 3 \text{ mod } 9
$$
**Scratch work:**
$$
\begin{align*}
x \equiv 3 \text{ mod } 9 &\iff 9 | (x - 3) \\
&\iff x - 3 = 9k \hspace{.2in} \text{ (for some $k \in \mathbb{Z}$)} \\
&\iff x = 9k - 3
\end{align*}
$$

### Operations on congruences

#### Addition/Subtraction

$$
a \equiv b \text{ (mod n) and } c \equiv d \text{ (mod n) } \implies  a + c \equiv b + d \text{ (mod n)} \tag{3.2}
$$

*Proof.*
$$
\begin{align*}
a \equiv b \text{ (mod n) } &\implies n | (a - b) \\
&\implies a - b = nk_1 \hspace{.2in} \text{ (for some $k_1 \in \mathbb{Z}$)} \\
&\implies a = nk_1 + b\\
c \equiv d \text{ (mod n) } &\implies n | (c - d) \\
&\implies c - d = nk_2 \hspace{.2in} \text{ (for some $k_2 \in \mathbb{Z}$)} \\
&\implies c = nk_2 + d \\
a + c &= nk_1 + b + nk_2 + d \\
&= n(k_1 + k_2) + (b + d) \\
&=nk + (b + d) \hspace{.2in} \text{(for some $k \in \mathbb{Z}$)} \\
&\implies (a + c) \text{ mod } n = b + d \\
&\implies a+c \equiv b + d \text{ (mod n)}
\end{align*}
$$

#### Multiplication

$$
a \equiv b \text{ (mod n) }  \implies ad \equiv bd \text{ (mod n)} \tag{3.3}
$$

*Proof.*
$$
\begin{align*}
a \equiv b \text{ (mod n) } &\implies n | (a - b) \\
&\implies a - b = nk_1 \hspace{.2in} \text{ (for some $k_1 \in \mathbb{Z}$)} \\
&\implies d(a - b) = d(nk_1) \\
&\implies da-db = n(dk_1) \\
&\implies n | (da-db) \\
&\implies da \equiv db \text{ (mod n)}
\end{align*}
$$
Next Theorem
$$
a \equiv b \text{ (mod n) and } c \equiv d \text{ (mod n) } \implies ac \equiv bd \text{ (mod n) }
$$
*Proof.*
$$
\begin{align*}
a \equiv b \text{ (mod n) } &\implies a = nk_1 + b \hspace{.2in} \text{ (for some $k_1 \in \mathbb{Z}$)} \\
c \equiv d \text{ (mod n)} &\implies  c = nk_2 + d \hspace{.2in} \text{ (for some $k_2 \in \mathbb{Z}$)} \\
a * c &= (nk_1 + b)(nk_2+d) \\
	  &=n^2k_1k_2 + bnk_2+dnk_1 +bd \\
	  &= n(nk_1k_2+bk_2+dk_2) + bd \\
	  &\implies ac \text{ mod } n = bd  \\
	  ac &\equiv bd \text{ (mod n)}
\end{align*}
$$

#### Division

Let us define division as so
$$
bb^{-1} \equiv 1 \text{ (mod n)} \\
$$
Theorem.
$$
ad \equiv bd \text{ (mod dn) } \iff a \equiv b \text{ (mod n) }
$$
*Proof.*
$$
\begin{align*} 
ad \equiv bd \text{ (mod dn) } &\implies  ad - bd = dnk \\
&\implies d(a-b) = d(nk) \\
&\implies a-b = nk \\
&\implies n | (a-b) \\
&\implies a \equiv b \text{ (mod n)}
\end{align*}
$$
