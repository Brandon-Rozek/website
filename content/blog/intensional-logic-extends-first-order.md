---
date: 2022-02-26 20:33:38-05:00
draft: false
math: true
medium_enabled: true
medium_post_id: 8e07b68aa8f5
tags: []
title: Intensional Logic Extends First Order
---

The second brightest object in the sky is known as the morgensteorra (morning star) and æfensteorra (evening star). Later on this object became known as Venus. [(Wikipedia)](https://en.wikipedia.org/wiki/Venus_in_culture)
$$
\text{morgensteorra} = \text{æfensteorra} = \text{venus}
$$
Gottlob Frege asks in 1892  whether we should make a distinction between a sense and a reference. [(SEP)](https://plato.stanford.edu/entries/logic-intensional/#Fre) [(Wikipedia)](https://en.wikipedia.org/wiki/Sense_and_reference)

One might be tempted to think that traditional first order logic can handle this. To show how we'll need to extend it, let us think of this problem from a cognitive perspective. Lets say that we have a relation $B$ that stands for belief. Now lets say that an agent has a belief that Venus is the evening star.
$$
B(\text{æfensteorra} = \text{venus})
$$
In first order logic, we can then deduce the following:
$$
B(\text{morgensteorra} = \text{venus})
$$
But does that make sense? It is possible to hold a belief that Venus is the evening star while not holding a belief that Venus is the morning star. Therefore, we cannot treat belief as a traditional relation symbol. Issues like these give birth to intensional reasoning and from that modal logic.