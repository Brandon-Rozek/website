---
title: "Algorithms in LaTex"
date: 2020-05-14T21:31:28-04:00
draft: false
tags: ["LaTex"]
---

There's a great package in LaTex called [`algorithm`](https://ctan.org/pkg/algorithms?lang=en) to help format psuedo-code algorithms for scientific papers. Here's a simple example of its usage:

```
\usepackage{algorithm}
\usepackage[noend]{algpseudocode}
\begin{algorithm}
\caption{Even Numbers}
\begin{algorithmic}[1]
\State Set variable $evens$ to an empty list.
\For {every integer $i$}
  \If {$i$ is divisible by $2$}
    \State Add $i$ to $events$ list.
  \EndIf
\EndFor
\end{algorithmic}
\end{algorithm}
```

![image-20200514225618784](/files/images/20200514225618784.png)