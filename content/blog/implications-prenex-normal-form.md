---
title: "Prenex Normal Form - Implication Exercise"
date: 2023-02-17T11:05:35-05:00
draft: false
tags: []
math: true
medium_enabled: false
---

I recently read through the Wikipedia article on [Prenex Normal Form](https://en.wikipedia.org/wiki/Prenex_normal_form). It first describes the two equivalences for conjunction/disjunction.
$$
(\forall x \phi) \vee \psi \iff \forall x(\phi \vee \psi) \tag{1.1}
$$

$$
(\exists x \phi) \vee \psi \iff \exists x (\phi \vee \psi) \tag{1.2}
$$

They show these rules similarly for conjunction. In the next section, they describe the rules for negation:
$$
\neg \exists x \phi \iff \forall x \neg \phi \tag{2.1}
$$

$$
\neg \forall x \phi \iff \exists x \neg \phi \tag{2.2}
$$

In the third section, they describe the rules related to implication. With it comes the following quote:

>  These rules can be derived by [rewriting](https://en.wikipedia.org/wiki/Rewriting#Logic) the implication $\phi \implies \psi$ as $\neg \phi \vee \psi$ and applying the rules for disjunction above.

This sounds like "we leave this as an exercise to the reader", and a reader I am! Let's label the rule in the quote as $0.1$.

**1.** Show that $(\forall x \phi) \implies \psi$ is equivalent to $\exists x (\phi \implies \psi)$
$$
\begin{align*}
(\forall x \phi) \implies \psi &\iff \neg (\forall x \phi) \vee \psi \tag{0.1} \\\\
&\iff (\exists x \neg \phi) \vee \psi \tag{2.2}\\\\
&\iff \exists x (\neg \phi \vee \psi) \tag{2.1}\\\\
&\iff \exists x (\neg \phi \implies \psi) \tag{0.1}
\end{align*}
$$
**2.** Show that $\phi \implies (\exists x \psi)$ is equivalent to $\exists x (\phi \implies \psi)$
$$
\begin{align*}
\phi \implies (\exists x \psi) &\iff \neg \phi \vee (\exists x \psi) \tag{0.1}\\\\
&\iff (\exists x \psi) \vee \neg \phi \tag{symmetry}\\\\
&\iff \exists x (\psi \vee \neg \phi) \tag{1.2}\\\\
&\iff \exists x (\neg \phi \vee \psi) \tag{symmetry}\\\\
&\iff \exists x (\phi \implies \psi) \tag{0.1}
\end{align*}
$$
