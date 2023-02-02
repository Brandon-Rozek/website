---
date: 2022-09-23 15:34:28-04:00
draft: false
math: false
medium_enabled: true
medium_post_id: d0a88900c580
tags:
- LaTex
title: 'Quick LaTex: Footnotes with no Counter'
---

Let's say there's a scenario where you want to have a footnote, but you don't want a counter associated with it. In order to stay consistent with the document style, the solution should use `\footnote` within its implementation.

The solution: Define `\blfootnote{text}` in the preamble.

```latex
\newcommand\blfootnote[1]{
    \begingroup
    \renewcommand\thefootnote{}\footnote{#1}
    \addtocounter{footnote}{-1}
    \endgroup
}
```

This makes use of the footnote command while also re-adjusting the footnote counts so that our variant doesn't increase it. We can then use this command within the document. Here's a beamer example:

```latex
\begin{frame}{Some Topic}
	This is where I explain some topic.
	\blfootnote{Numberless Footnote}
\end{frame}
```

Complete Minimal Example:

```latex
\documentclass[aspectratio=169]{beamer}
\usepackage[utf8]{inputenc}
\usetheme{Copenhagen}

\newcommand\blfootnote[1]{
    \begingroup
    \renewcommand\thefootnote{}\footnote{#1}
    \addtocounter{footnote}{-1}
    \endgroup
}

\begin{document}

\begin{frame}{Some Topic}
	This is where I explain some topic.
	\blfootnote{Numberless Footnote}
\end{frame}

\end{document}

```