---
title: "Comparator Logic Gate"
date: 2021-06-18T01:09:45-04:00
draft: false
tags: []
math: true
medium_enabled: true
---

This post is heavily derived from the Wikipedia post on [Digital Comparators](https://en.wikipedia.org/wiki/Digital_comparator) and therefore can be distributed under the Creative Commons Attribution-ShareAlike 3.0 license.

To compare two binary numbers, we need to find a way to check if two single bits are equal or if one is greater than the other.

## Checking Single Bit Equality

Let's construct the truth table:

| A    | B    | $A = B$ |
| ---- | ---- | ------- |
| 0    | 0    | 1       |
| 1    | 0    | 0       |
| 0    | 1    | 0       |
| 1    | 1    | 1       |

The only two ways this evaluates to true is if

- A is 1 and B is 1
- A is 0 and B is 0

Therefore,
$$
(A = B) \equiv AB + \bar{A}\bar{B} \equiv \overline{(A \oplus B)}
$$

## Single Bit Comparator

To check if one bit is greater than the other, let us first look at the truth table:

| A    | B    | $\bar{B}$ | $A > B$ |
| ---- | ---- | --------- | ------- |
| 0    | 0    | 1         | 0       |
| 1    | 0    | 1         | 1       |
| 0    | 1    | 0         | 0       |
| 1    | 1    | 0         | 0       |

The only way for this to evaluate to true is if A is 1 and B is 0. That is $(A > B) \equiv A\bar{B}$



## L-Bit Comparator

To compare an entire bitstring, we start from the most significant bit and check to see if one bit is greater than the other. If not, it will then check the next bit while confirming that all the previous bits were the same. For a 3-bit comparator, the logic will look like the following:
$$
(A_3A_2A_1 > B_3 B_2 B_1) \equiv A_3\bar{B_3} + \overline{(A_3 \oplus B_3)}A_2\bar{B_2} + \overline{(A_3 \oplus B_3)}\overline{(A_2 \oplus B_2)}A_1\bar{B_1} 
$$
