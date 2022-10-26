---
title: "Speaker Notes in LaTex Beamer"
date: 2022-10-25T21:43:38-04:00
draft: false
tags: ["LaTex"]
math: false
---

I often struggle with deciding how much content to put on my slides. Personally, I feel that my slides should be self-contained so that others can review them afterwards. This was especially true when I held [recitations](https://brandonrozek.com/ta/spring2022/csci2600/) as a TA.

What if instead of putting all the content into one slide, we can have a corresponding notes document? Crazy enough, Beamer comes to the rescue! 

Within a frame in beamer, we can add a `\note[item]{X}` call, and the contents of `X` will appear in a bullet point within a corresponding speaker notes slide.

Let's see how this works in action.

```latex
\documentclass{beamer}

%\setbeameroption{hide notes} % Only slides
%\setbeameroption{show only notes} % Only notes
\setbeameroption{show notes on second screen=right} % Both

\title{Speaker notes within Beamer}
\author{}\date{}

\begin{document}

\begin{frame}
  \titlepage
  \note[item]{Welcome to the talk!}
  \note[item]{As you can see, this slidedeck is a work in progress.}
\end{frame}

\end{document}
```

This code results in:

![Image of slide with speaker notes shown on the right side](/files/images/blog/20221025220326.png)

In this mode, the slide is shown on the left side of the page while the speaker notes on shown on the right side. The comments in the code suggest that this isn't the only way to do this! You can produce a PDF version with only the slides and one with only the notes as well!

With this, I am thinking of distributing slides that I'm presenting more ahead of time. There are several benefits that I can immediately see in using the speaker notes feature:

- Get to keep slides minimal
- Keep answers away from the live audience, with an easy way to distribute aftewards
- Not forget any points you want to address

If you want to learn more features within LaTex beamer, I suggest checking out their [package documentation](http://mirrors.ctan.org/macros/latex/contrib/beamer/doc/beameruserguide.pdf). It's surprisingly written accessibly, with many presentation tips within.
