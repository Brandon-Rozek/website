---
title: "Multi-Column slides in Beamer"
date: 2022-01-26T23:29:31-05:00
draft: false
tags: ["LaTex"]
math: false
---

When creating slides in LaTex Beamer, it can be frustrating to not have the easy ability to drag text boxes around. Luckily, creating a multi-column layout in Beamer is not difficult! Below is an example of a two column slide layout, where the left side is a bulleted list, and the right side is an image:

```latex
\documentclass{beamer}
\usepackage[utf8]{inputenc}

% Beamer Packages
\usepackage{harvard}
\usetheme{Copenhagen}


\begin{document}

\begin{frame}{About Me}
\begin{columns}

% Column 1
\column{.5\linewidth}
\begin{itemize}
    \item Enjoy going on short hikes.
    \item Forgetful at times and writes blog posts to jog my memory.
\end{itemize}

% Column 2
\column{.5\linewidth}
\centering
\includegraphics[width=4cm]{images/avatar.jpg}

\end{columns}
\end{frame}
\end{document}
```

![](/files/images/202201262338.svg)