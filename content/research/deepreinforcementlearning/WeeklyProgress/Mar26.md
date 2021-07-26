---
title: Progress for Week of March 26
showthedate: false
math: true
---

## Parallelized Evolutionary Strategies

When the parallel ES class is declared, I start a pool of workers that then gets sent with a loss function and its inputs to compute whenever calculating gradients.

## Started Exploring Count-Based Exploration

I started looking through papers on Exploration and am interested in using the theoretical niceness of Count-based exploration in tabular settings and being able to see their affects in the non-tabular case.

""[Unifying Count-Based Exploration and Intrinsic Motivation](https://arxiv.org/abs/1606.01868)" creates a model of a arbitrary density model that follows a couple nice properties we would expect of probabilities. Namely, $P(S) = N(S) / n$ and $P'(S) = (N(S) + 1) / (n + 1)$. Where $N(S)$ represents the number of times you've seen that state, $n$ represents the total number of states you've seen, and $P'(S)$ represents the $P(S)$ after you have seen $S$ another time. With this model, we are able to solve for $N(S)$ and derive what the authors call a *Psuedo-Count*. 
