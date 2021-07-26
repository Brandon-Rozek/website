---
title: Revisiting Similarity Measures
showthedate: false
math: true
---

## Manhatten Distance

An additional use case for Manhatten distance is when dealing with binary vectors. This approach, otherwise known as the Hamming distance, is the number of bits that are different between two binary vectors.

## Ordinal Variables

Ordinal variables can be treated as if they were on a interval scale.

First, replace the ordinal variable value by its rank ($r_{if}$) Then map the range of each variable onto the interval $[0, 1]$ by replacing the $f_i$ where f is the variable and i is the object by 
$$
z_{if} = \frac{r_{if} - 1}{M_f - 1}
$$
Where $M_f$ is the maximum rank.

### Example

Freshman = $0$ Sophmore = $\frac{1}{3}$ Junior = $\frac{2}{3}$  Senior = $1$

$d(freshman, senior) = 1$

$d(junior, senior) = \frac{1}{3}$

