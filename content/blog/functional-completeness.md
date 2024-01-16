---
title: "Functional Completeness"
date: 2023-05-30T07:30:08-04:00
draft: false
tags:
    - Logic
math: true
medium_enabled: false
---

You might have heard somewhere that AND as well as NOT are the only two operators you need in propositional logic in order to represent all possible truth tables. 

This is often used to simplify circuit design. Instead of having a custom chip for every other operator, it's generally more cost effective to only have two distinct chips but use more of them. But what if we want to find other combinations? 

In formal terms, we're looking for other [functional complete](https://en.wikipedia.org/wiki/Functional_completeness) sets.

In this post, we'll provide an overview for finding these sets. Finding some examples of functional complete sets along the way.

---

The intuition here is to know that our set $\mathcal{S}$ is functionally complete if we can replicate the other operators using the ones only within $\mathcal{S}$. Let's refresh ourselves in what the complete set of operators are:
$$
\\\{\mathtt{AND}, \mathtt{OR}, \mathtt{NOT}, \mathtt{IF}, \mathtt{IFF}\\\}
$$
The first step would normally be to remove one operator from the above set and see if you can derive it using the other operators. For brevity of this post though, we'll skip sets of length four and look directly at sets of length three.

**Example 1:** Show that $\mathcal{S} = \\\{\mathtt{AND}, \mathtt{OR}, \mathtt{NOT}\\\}$ is functionally complete.

In this example, we're missing both $\mathtt{IF}$ and $\mathtt{IFF}$. Using the operators of $\mathcal{S}$ we can define the missing operators to be (in prefix notation):
$$
\begin{align*}
(\mathtt{IF}~A~B) &\equiv (\mathtt{OR}~(\mathtt{NOT}~A)~B) \\\\
(\mathtt{IFF}~A~B) &\equiv (\mathtt{AND}~(\mathtt{OR}~A~B) (\mathtt{OR}~(\mathtt{NOT}~A)~ (\mathtt{NOT}~B)))
\end{align*}
$$
For now, it'll be beyond the scope on how to find the correct combination of operators within $\mathcal{S}$.

Since we're able to represent the missing operators in $\mathcal{S}$ the set is functionally complete.

**Example 2:** Show that $\mathcal{S} = \\\{\mathtt{NOT},  \mathtt{AND}, \mathtt{IF}\\\}$ is functionally complete.

We have to show that we can represent the missing operators $\mathtt{OR}$ and $\mathtt{IFF}$ using only elements of $\mathcal{S}$.
$$
\begin{align*}
(\mathtt{IFF}~A~B) &\equiv (\mathtt{AND}~ (\mathtt{IF}~ A~ B)~ (\mathtt{IF}~ B~ A)) \\\\
(\mathtt{OR}~ A~ B) &\equiv (\mathtt{NOT}~ (\mathtt{AND}~ (\mathtt{NOT}~ A)~ (\mathtt{NOT}~ B)))
\end{align*}
$$
This shows that the set $\mathcal{S}$ is functionally complete.

At this point we know that $\\\{\mathtt{AND}, \mathtt{OR}, \mathtt{NOT}\\\}$ and $\\\{\mathtt{NOT},  \mathtt{AND}, \mathtt{IF}\\\}$ are functionally complete. Now comes the exciting part, finding functionally complete sets with only two operators.

- What knowledge can we derive from $\\\{\mathtt{AND}, \mathtt{OR}, \mathtt{NOT}\\\}$?

Let's consider all possible sets of length two:
$$
\\\{\mathtt{AND}, \mathtt{NOT}\\\} \\\\
\\\{\mathtt{AND}, \mathtt{OR}\\\} \\\\
\\\{\mathtt{OR}, \mathtt{NOT}\\\}
$$
**Example 3:** Is $\{\mathtt{AND}, \mathtt{NOT}\}$ functionally complete?

We need to show that we can derive $\mathtt{OR}$.
$$
(\mathtt{OR}~ A~ B) \equiv (\texttt{NOT}~ (\texttt{AND}~ (\texttt{NOT}~ A)~ (\texttt{NOT}~ B)))
$$
This means using only $\mathtt{AND}$ and $\mathtt{NOT}$ we can represent $\\\{\mathtt{AND}, \mathtt{OR}, \mathtt{NOT}\\\}$ which is functionally complete. Therefore, $\mathcal{S} = \\\{ \mathtt{AND}, \mathtt{NOT}\\\}$ is functionally complete.

**Example 4:** Is $\\\{\mathtt{AND}, \mathtt{OR}\\\}$ functionally complete?

No, because we cannot represent $\mathtt{NOT}$ using both $\mathtt{AND}$ and/or $\mathtt{OR}$. In a future iteration of this point I might describe why this is the case.

**Example 5:** Is $\mathcal{S} = \\\{\mathtt{OR}, \mathtt{NOT}\\\}$ functionally complete?

We need to show that we can derive $\mathtt{AND}$.
$$
(\mathtt{AND}~ A~ B) \equiv (\texttt{NOT}~ (\texttt{OR}~ (\texttt{NOT}~ A)~ (\texttt{NOT} ~B))
$$
Therefore, $\mathcal{S}$ is functionally complete.

Similarly, we can look at $\\\{\mathtt{NOT}, \mathtt{AND}, \mathtt{IF}\\\}$ and consider pairs of operators that might still be functionally complete.

**Example 6:** Is $\\\{\mathtt{AND}, \mathtt{IF}\\\}$ functionally complete?

No, because you cannot represent $\mathtt{NOT}$.

**Example 7:** Is $\\\{\mathtt{NOT}, \mathtt{IF}\\\}$ functionally complete?

Here we're missing $\mathtt{AND}$, so if we can derive it using the two operators, then the set is functionally complete.
$$
(\mathtt{AND}~ A~ B) \equiv (\mathtt{NOT}~ (\mathtt{IF}~ A~ (\mathtt{NOT}~ B)))
$$

---

There are no single operators that are functionally complete in this example. Though the above gives somewhat of a procedure for finding all the sets of functionally complete operators. Here's a summary:

1. Start with your base set of operators $\mathcal{S} = \{x_1, x_2, \dots, x_n\}$
2. Remove $x \in \mathcal{S}$ such that $\mathcal{S}^\prime = \mathcal{S} - \{x\}$
3. Derive $x$ using the other operators in $\mathcal{S}^\prime$. 
4. If possible, add $\mathcal{S}^\prime$ to $\mathcal{S}_{n - 1}$ the set of functionally complete operators of length $n - 1$
5. Repeat steps (2) and (3) on each $\mathcal{S}^\prime \in \mathcal{S}_{n - 1}$ to create $\mathcal{S}\_{n - 2}$ 
6. Keep going until no new functionally complete sets are found.

I know that this is a high level article and that there's some details that are left out, but please feel free to reach out if you have any questions.
