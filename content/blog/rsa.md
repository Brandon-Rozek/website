---
title: RSA Cryptography
date: 2019-12-10T22:15:21-05:00
draft: false
images: []
math: true
tags: ["Security"]
---

# Introduction

Why do we need Cryptography? Well let's say Bob is purchasing things from Alice over the internet. He wants to give Alice his credit card details to complete his transaction, but he feels uncomfortable with the thought that others can possibly read it as well. RSA is a cryptosystem that underlies HTTPS, and this gives Bob a sense of security that only Alice can see his message.

The journey of RSA starts in 1976 when Whitfield Diffie and Martin Hellman published  a framework describing an asymmetric public-private key cryptosystem through four key steps:

1. Key Generation
2. Key Distribution
3. Encryption with one-way function (using a public key)
4. Decryption (using a private key)

They left the one-way function undefined, making it an open problem for the community. Ron **R**ivest, Adi **S**hamir, and Leonard **A**dleman at MIT took up this challenge. Rivest and Shamir were Computer Scientists trying to come up with this function while Adleman was the mathematician tasked with finding flaws in their discoveries. After working together to develop the RSA cryptosystem in 1977, Rivest, Shamir, and Adleman went on to found the organization RSA Data Security in 1982. 

# RSA Algorithm

In this section, we'll look at the RSA algorithm through the lens of the four steps listed in the previous section.

#### Key Generation

Alice needs to generate public and private keys through the following method:

1. Choose two distinct prime integers $p$ and $q$.
2. Compute $n = pq$. The integer $n$ will be later released as part of the *public key*.
3. Calculate $\phi(n)$ which by the Euler's Totient Product of Primes property is $(p - 1)(q - 1)$.
4. Choose $e \in \mathbb{Z}$ such that $e$ and $\phi(n)$ are relatively prime. The integer $e$ will also be released as part of the *public key*.
5. Calculate $d$, the multiplicative inverse of $e$ modulo $\phi(n)$. The integer $d$ will be kept secret as the *private key*.

#### Key Distribution

For Bob to send a message to Alice, he will need to know Alice's public key $n$ and $e$. Bob, however, does not need to know Alice's prime integers $p$ and $q$ that divide $n$. Nor does he need to know the private key $d$.

#### Encryption

Let $m \in \mathbb{Z}_n$ be the message that Bob wants to send. Bob calculates this number from his message using an agreed-upon reversible algorithm. The ciphertext or encrypted block $c$ is computed by, $c \equiv m^e$ (mod $n$). Bob then sends the ciphertext to Alice.

#### Decryption

Alice receives this ciphertext $c$ from Bob and then can recover the original message $m$ by computing $c^d$ modulo $n$. How is this possible? Well recall that $c^d \equiv (m^e)^d$. Then, $c^d \equiv m^{ed}$ by exponent rules. Recall that $e$ and $d$ are multiplicative inverses modulo $\phi(n)$. Therefore by definition, $ed = 1 + \phi(m)t$ for some $t \in \mathbb{Z}$. Then,

\begin{align*}
c^d &\equiv m^{1 + \phi(n)t} \\\\
    &\equiv m(m^{\phi(n)})^t
\end{align*}

Well since $n$ is prime, by Euler's Theorem $m^{\phi(n)} \equiv 1$ modulo $n$. Thus, $c^d \equiv m \cdot 1^t \equiv m$ modulo $n$. Through this short proof, we can see that Alice successfully retrieves Bob's message $m$ just by raising the ciphertext $c$ to the power of the private key $d$.

## Example

Let's run through a short example of this algorithm with small integers. Let $p = 3, q = 5$. Then $n = pq = 15$. We then calculate $\phi(n) = \phi(p)\phi(q) = 2(4) = 8$. An integer $e$ that is relatively prime to $\phi(n)$ is $11$. Finally we compute the inverse of $e$ modulo $\phi(n)$.

\begin{align*}
11d &\equiv 1 \text{ (mod $8$) } \\\\
11d &\equiv 33 \text{ (mod $8$)} \\\\
d &\equiv 3 \text{ (mod $8$)}
\end{align*}


Alice then gives Bob the integers $n = 15$ and $e = 11$. Bob can then encode his message (say $m = 12$) by raising $m$ to the power of $e$. Thus, $c = m^e = 12^{11} = 743008370688 \equiv 3$ modulo 15. Alice can then recover $m = 12$ by raising $c = 3$ to the power of her private key $d$. $m \equiv c^d \equiv 3^3 \equiv 27 \equiv 12$ modulo $15$. 


# Discussion

Well if it's this simple to calculate, why is it secure? It is actually extremely difficult to factor a large prime number $n$. If $n$ can be factored into $p$ and $q$, then it is easy to compute $d \equiv e^{-1}$ modulo $\phi(pq)$. It is also really hard to efficiently solve for $m$ in the congruence $c \equiv m^e$ modulo $n$. RSA Laboratories on March 1991 issued a challenge tasking the public to calculate prime factors of $n$ (called RSA numbers) of increasing digits. They offered a cash prize of up to \$200,000 for solving RSA-2048 which is a 617 digit long number. As of the time of the presentation, the largest factored RSA number was RSA-768 (768 bits or 232 decimal digits) which was calculated over the span of two years. As of the time of this writing, towards the end of this year (2019) the largest known factored RSA number is actually RSA-240 (795 bits or 240 decimal digits). Currently the National Institute of Standards and Technology (NIST) recommends the use of 2048-bit keys for use in RSA. So for the time being, our communications are safe.


