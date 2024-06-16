---
title: "Quick Beamer: Generating a slide at the beginning of each section"
date: 2024-06-15T19:26:27-07:00
draft: false
tags: ["LaTex"]
math: false
medium_enabled: false
---

People want to know where they are within your presentation. This is why for a class of long presentations, there's an outline slide in the beginning and section headers.

Separating sections with an additional slide is nice because it not only gives an audience an opportunity for questions, but it also allows you to sneak in a sip of water.

To accomplish this automatically, thanks to a tip from [James Oswald](https://jamesoswald.dev), we add the following to the preamble of our Beamer file (before the `\begin{document}`)

```latex
\AtBeginSection[]{
  \begin{frame}
  \vfill
  \textbf{\insertsectionhead}
  \vfill
  \end{frame}
}
```

This produces the following slide right after your `\section{}` code:

![Image of beamer slide with the section text in bold](/files/images/blog/20240615193803.png)

Which for me and my template is equivalent to if I typed this in the beginning of each section:

```latex
\begin{frame}
	\textbf{First Awesome Section}
\end{frame}
```

Saving a little bit of typing is always nice :)

My slide is fairly bare-bones, another cool approach [shows the entire table of contents with every other section faded out.](https://statisticaloddsandends.wordpress.com/2019/02/18/beamer-inserting-section-slides-before-each-section/)

