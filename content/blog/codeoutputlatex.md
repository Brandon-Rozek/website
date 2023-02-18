---
date: 2022-01-27 09:15:10-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: c4d061953056
tags:
- LaTex
title: Code alongside Output in LaTex
---

Working on a tool paper, I had the desire to share code alongside its output. With a combination of the `listings`, `caption`, and `color` packages, we can get a result that's nice looking.

The imports needed

```latex
\usepackage{color}
\usepackage{listings}
\usepackage{caption}
```

I want a think topbar that labels which column is the code section and which column is the output section.

```latex
\DeclareCaptionFormat{listing}
    {\colorbox[cmyk]{0.73, 0.35, 0.15,.5}
    {\parbox{\textwidth}{#1#2#3}}}
\DeclareCaptionFont{white}{\color{white}}
\captionsetup[lstlisting]{
    format=listing,
    labelfont=white,
    textfont=white,
    font={bf,footnotesize}
}
```

Next I define some colors that I would like to use as the theme for the code output:

```latex
\definecolor{keyblue}{rgb}{0.1, 0.1, 0.6}
\definecolor{dkgreen}{rgb}{0,0.6,0}
\definecolor{gray}{rgb}{0.5,0.5,0.5}
\definecolor{stringcol}{rgb}{0.58,0.4,0.1}
```

Setup for the code output

```latex
\lstset{
  language=Python,
  columns=flexible,
  basicstyle={\small\ttfamily},
  keywordstyle=\color{keyblue},
  commentstyle=\color{dkgreen},
  stringstyle=\color{stringcol},
  breaklines=true,
  breakatwhitespace=true,
  tabsize=4
}
```

Then inside the document, you can use `minipage` to setup a two column layout.

```latex
% Column 1: Code
\begin{minipage}[t]{.45\textwidth}
\begin{lstlisting}[title=Code]
def factorial(n):
    if n == 0:
        return 1
    return n * factorial(n - 1)
# Let's test it out!
print(factorial(5))
\end{lstlisting}
\end{minipage}
% Column 2: Output
\begin{minipage}[t]{.45\textwidth}
\begin{lstlisting}[title=Output]
    120
\end{lstlisting}
\end{minipage}
```

 ![](/files/images/blog/202201292013.svg)

Below is all these steps combined into a compile-able LaTex file.


```latex
\documentclass{article}
\usepackage[utf8]{inputenc}

% Imports
\usepackage{color}
\usepackage{listings}
\usepackage{caption}

% Define colors
\definecolor{keyblue}{rgb}{0.1, 0.1, 0.6}
\definecolor{dkgreen}{rgb}{0,0.6,0}
\definecolor{gray}{rgb}{0.5,0.5,0.5}
\definecolor{stringcol}{rgb}{0.58,0.4,0.1}

% Caption Setup
\DeclareCaptionFormat{listing}
    {\colorbox[cmyk]{0.73, 0.35, 0.15,.5}
    {\parbox{\textwidth}{#1#2#3}}}
\DeclareCaptionFont{white}{\color{white}}
\captionsetup[lstlisting]{
    format=listing,
    labelfont=white,
    textfont=white,
    font={bf,footnotesize}
}

% Code listing setup
\lstset{
  language=Python,
  columns=flexible,
  basicstyle={\small\ttfamily},
  keywordstyle=\color{keyblue},
  commentstyle=\color{dkgreen},
  stringstyle=\color{stringcol},
  breaklines=true,
  breakatwhitespace=true,
  tabsize=4
}


\begin{document}

% Column 1: Code
\begin{minipage}[t]{.45\textwidth}
\begin{lstlisting}[title=Code]
def factorial(n):
    if n == 0:
        return 1
    return n * factorial(n - 1)
# Let's test it out!
print(factorial(5))
\end{lstlisting}
\end{minipage}
% Column 2: Output
\begin{minipage}[t]{.45\textwidth}
\begin{lstlisting}[title=Output]
    120
\end{lstlisting}
\end{minipage}

\end{document}

```