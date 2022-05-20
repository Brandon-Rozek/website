---
title: "On Writing Simple Scripts"
date: 2022-05-19T20:40:19-04:00
draft: false
tags: []
math: false
---

I generally prefer a simpler solution to a problem if possible. This comes especially true with scripting. If I write a small script for something like say my website I generally have three requirements of the system:

- No dependencies outside the language
- Language is interpreted (I don't want to worry about build dependencies)
- Comes preinstalled on systems I care about

I primarily work on Linux systems and very rarely don't. Therefore, the simplest scripting language for me to write in is Bash. In fact, I generally reach for that first. If what I need to do is sufficiently complicated, then the next language I'll reach for is Python.

Though that begs the question, what is sufficiently complicated? Here are some tasks that I don't think Bash is suited for:

- Data Parsing
  - I know `ack`, `sed`, and `grep` exist, but they're complicated and unintuitive to use. We write programs for *people first*, computers second.
  - Harder to parse JSON. The program `jq` exists but that's not part of the GNU coreutils.
- Math
  - I believe `bc` is the easiest command to use to process arithmetical expressions. Though this also then involves constructing strings to pass into bc. For example: `result=$(echo "1 + 5" | bc)`
- Anything requiring abstract data types
  - (Associative) arrays in bash are scary to me
  - Slawomir's functional programming in [bash library](https://github.com/ssledz/bash-fun) makes it more bearable. ([My fork](https://github.com/Brandon-Rozek/bashfun))
- Argument Parsing
  - Attempted to [parse arguments in bash](/blog/bashpartialargparse/), but [parsing arguments in Python](/blog/python-argpase/) is much cleaner to me.

So why Python? 

- Comes preinstalled on most Linux systems as they're often used in desktop environments
- Currently has developer mindshare so others are apt to understand the scripts

Both those reasons are likely to make it so that my choice will change over time. Perl used to be the very popular choice for scripting...

