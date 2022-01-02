---
title: "Code in LaTex"
date: 2020-04-30T23:46:05-04:00
draft: false
tags: ["LaTex"]
---

I am currently working on a paper in LaTex and wanted to include some source code in it. I didn't want to use the default `verbatim` environment since I wanted to include syntax highlighting as well. Luckily, the `listings` package is an easy and extensible way to include source code inside LaTex documents. To speak first of its extensibility, here is a subset of the arguments that it can possibly take:

| Argument          | Description                                                  |
| ----------------- | ------------------------------------------------------------ |
| aboveskip         | Amount of space to include above code.                       |
| backgroundcolor   | Background color                                             |
| basicstyle        | Font-style of code (Color & Size)                            |
| belowskip         | Amount of space to include below code.                       |
| breakatwhitespace | Only break at whitespace (boolean)                           |
| breaklines        | Automatic Line Breaking (boolean)                            |
| commentstyle      | Font-style of comments (Color & Size)                        |
| frame             | Type of frame: `l` for left, `r` for right, `t` for top, `b` for bottom; can use combination of letters or `single`. |
| keywordstyle      | Font-style of keywords (Color & Size)                        |
| language          | Language of code (for highlighting purposes)                 |
| numbers           | Where to put the numbers: `none`, `left`, or `right`.        |
| numbersep         | How far the line-numbers are from the code.                  |
| numberstyle       | Font-style of numbers (Color & Size)                         |
| stringstyle       | Font-style of strings in code (Color & Size)                 |
| tabsize           | Default tab size in terms of spaces.                         |
| title             | Show filename included in `\lstinputlistings` or caption.    |

Here is an example of code that I used in a paper

```latex
\usepackage{color}
\usepackage{listings}
\definecolor{keyblue}{rgb}{0.1, 0.1, 0.6}
\definecolor{dkgreen}{rgb}{0,0.6,0}
\definecolor{gray}{rgb}{0.5,0.5,0.5}
\definecolor{stringcol}{rgb}{0.58,0.4,0.1}

\lstset{frame=l,
  language=Python,
  aboveskip=3mm,
  belowskip=3mm,
  columns=flexible,
  basicstyle={\small\ttfamily},
  numbers=left,
  numberstyle=\tiny\color{gray},
  numbersep=2mm,
  keywordstyle=\color{keyblue},
  commentstyle=\color{dkgreen},
  stringstyle=\color{stringcol},
  breaklines=true,
  tabsize=4
}

\begin{lstlisting}
def greeting():
	return "Hello!"

# Printing the greeting to the screen
print(greeting())
\end{lstlisting}
```

![image-20200501001231572](/files/images/20200501001231572.png)