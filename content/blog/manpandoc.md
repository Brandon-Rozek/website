---
title: "Man Pages with Pandoc"
date: 2019-11-07T21:42:08-05:00
draft: false
---

[Ethan Martin](https://emar10.dev) recently showed off the Pandoc tool to me. In case you don't know, Pandoc is a swiss-army knife of markup languages. It allows you to easily convert from one markup language to another. 

This got me thinking my love for Markdown as the lowest common denominator for my notes. I can write markdown files for my website, for presentations, and output it into PDF and Word. Of course you don't get to have the fine control as you do with Latex, but with document classes, you can at least theme it any way you like!

Now to focus this blog post, I do want to share one really cool feature I found out about Pandoc. It can create man pages. I thought of this as a great way to create documentation for a software project. I'll give you an example to kick things off.

Note: The content is stolen from the `git` man page.

```markdown
---
title: git
section: 1
header: Git Manual
---

# NAME
  git - the stupid content tracker

# SYNOPSIS
  git `[--version] [--help]`

# DESCRIPTION
  Git is a fast, scalable, distributed revision control system with an unusually rich command set that provides both high-level operations and full access to internals.

  See **gittutorial**(7) to get started, then see **giteveryday**(7) for a useful minimum set of commands. The **Git User’s Manual**[1] has a more in-depth introduction.

  After you mastered the basic concepts, you can come back to this page to learn what commands Git offers. You can learn more about individual Git commands with "git help command". **gitcli**(7) manual page gives you an overview of the command-line command syntax.

  A formatted and hyperlinked copy of the latest Git documentation can be viewed at **https://git.github.io/htmldocs/git.html**.

# OPTIONS
  --version
    Prints the Git suite version that the git program came from.

  --help
    Prints the synopsis and a list of the most commonly used commands. If the option --all or -a is given then all available commands are printed. If a Git command is named this option will bring up the manual page for that command.

  Other options are available to control how the manual page is displayed. See git-help(1) for more information, because git --help ...  is converted internally into git help ....
```

Then execute

```bash
pandoc -s -t man -o git.1 git.md
```

Here's what the command means: "Run `pandoc` on standalone mode converting `git.md` into a man page called `git.1`"

To see the results run `man ./git.1`

![1573183066061](/files/images/blog/1573183066061.png)

