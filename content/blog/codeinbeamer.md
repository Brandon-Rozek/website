---
title: "Code in LaTex Beamer"
date: 2022-01-26T23:11:37-05:00
draft: false
tags: ["LaTex"]
math: false
---

I commonly use the [`listings` package](/blog/latexcode/) to showcase code in my LaTex documents. I tried doing the same in my Beamer slidedecks and I ran into an issue where the LaTex source code failed to compile. After digging around, I figured out its because every slide or frame that includes code (or any verbatim environment) needs to be marked as `fragile`. A minimal example is presented below:

```latex
\documentclass{beamer}
\usepackage[utf8]{inputenc}

% Beamer Packages
\usepackage{harvard}
\usetheme{Copenhagen}

% Code Rendering Packages
\usepackage{listings}
\lstset{
  language=Java,
  columns=flexible,
}

% Begin Slidedeck
\begin{document}
\begin{frame}[fragile]{Code Example}
    \begin{lstlisting}
    int x = 5;
    \end{lstlisting}
\end{frame}
\end{document}
```

