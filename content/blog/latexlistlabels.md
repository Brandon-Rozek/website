---
title: "LaTex List Labels"
date: 2022-01-16T23:17:51-05:00
draft: false
tags: ["LaTex"]
math: false
---

A quick tip that I recently learned is that the symbols in a LaTex list item is changeable. In fact, the following technique works for both the `enumerate` and `itemize` environments.

```latex
\begin{itemize}
    \item[$\square$]  Item 1
    \item[$\triangle$] Item 2
\end{itemize}

\begin{enumerate}
	\item[$\rho_1$] Property 1
	\item[$\rho_2$] Property 2
	\item[$\rho_3$] Property 3
\end{enumerate}
```

![](/files/images/202201162357.svg)
