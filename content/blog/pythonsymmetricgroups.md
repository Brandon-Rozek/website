---
title: "Symmetric Groups in Python"
date: 2019-05-22T20:02:21-04:00
draft: false
tags: [ "Math", "Python" ]
math: true
---

**Warning:** This post is meant for someone whose familiar with concepts of Abstract Algebra.

## Refresher

### Definitions

An **operation** on a set is a calculation that maps one element in a set onto another element of the set. 

A **group** in mathematics is a set and an operation that follows the three properties:

- There exists an identity element.
- The operation is associative.
- For every element, there exists an inverse of that element in the set.

**Symmetric Groups** are groups whose elements are all bijections from the set onto itself and operation which is composition of functions.

### Example

Let's look at the group $\mathbb{Z}_3$. Here is an example of an element of its symmetric group.
$$
\begin{pmatrix}
0 & 1 & 2 \\
1 & 2 & 0
\end{pmatrix}
$$
This element maps $0 \rightarrow 1$, $1 \rightarrow 2$, and $2 \rightarrow 0$.

A good way to check if something similar to the above is an element of a symmetric group is pay attention to the second row. Make sure that it only contains the elements of the set you care about (ex: $\mathbb{Z}_3$) and that there are no repeats.

Let's look at an example of composing two elements from this symmetric group.

$$
\begin{pmatrix}
0 & 1 & 2 \\
1 & 2 & 0
\end{pmatrix}
\circ
\begin{pmatrix}
0 & 1 & 2 \\
0 & 2 & 1 \\
\end{pmatrix}
\=
\begin{pmatrix}
0 & 1 & 2 \\
1 & 0 & 2 \\
\end{pmatrix}
$$

The main thing to remember here is that you must compose from right to left.

$0 \rightarrow 0$ and then $0 \rightarrow 1$, so ultimately $0 \rightarrow 1$.

$1 \rightarrow 2$ and $2 \rightarrow 0$, so ultimately $1 \rightarrow 0$.

$2 \rightarrow 1$ and $1 \rightarrow 2$, so ultimately $2 \rightarrow 2$.

### Finding Inverses

Finding the inverse is simple, since all you need to do is flip the two rows and sort it again.
$$
\begin{pmatrix}
0 & 1 & 2 \\
1 & 2 & 0
\end{pmatrix}^{-1} =
\begin{pmatrix}
1 & 2 & 0 \\
0 & 1 & 2
\end{pmatrix} = 
\begin{pmatrix}
0 & 1 & 2 \\
2 & 0 & 1
\end{pmatrix}
$$

 ### Code Implementation

For Abstract Algebra homework, there was a lot of compositions of these symmetric elements. Sadly, I get pretty lazy doing these by hand for many hours. So like any Computer Scientist, I created a simple script in Python to help me compute these.

The code is located in [this gist](https://gist.github.com/Brandon-Rozek/adf9e1e64e2fbfcd3f8d3bc5da9322bf).

#### Basic Usage

`SymmetricElement` takes in the second row of the matrices we were playing with. You can find the inverse with `element.inverse()` and you can compose two symmetric elements together with the `*` operation.

```python
SymmetricElement(1,2,3)
# array([[1., 2., 3.],
#       [1., 2., 3.]])
```

```python
SymmetricElement(1,2,3) * SymmetricElement(2,1,3)
#array([[1., 2., 3.],
#       [2., 1., 3.]])

```

```python
SymmetricElement(1,2,3).inverse()
#array([[1., 2., 3.],
#       [1., 2., 3.]])
```



