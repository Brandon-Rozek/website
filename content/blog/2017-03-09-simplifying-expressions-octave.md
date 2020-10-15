---
id: 2115
title: Simplifying Expressions with Octave
date: 2017-03-09T02:09:58+00:00
author: Brandon Rozek
layout: post
guid: https://brandonrozek.com/?p=2115
permalink: /2017/03/simplifying-expressions-octave/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
mf2_syndicate-to:
  - 'a:1:{i:0;s:22:"bridgy-publish_twitter";}'
mf2_cite:
  - 'a:4:{s:9:"published";s:25:"0000-01-01T00:00:00+00:00";s:7:"updated";s:25:"0000-01-01T00:00:00+00:00";s:8:"category";a:1:{i:0;s:0:"";}s:6:"author";a:0:{}}'
tumblr_post_id:
  - "158172999969"
mf2_syndication:
  - 'a:1:{i:0;s:60:"https://twitter.com/B_RozekJournal/status/839659534146801665";}'
format: aside
kind:
  - note
---
Octave is a high level programming language intended for numerical computations. One of the cool features of this is that with symbolic expressions, you can then simplify mathematical expressions.

<!--more-->

## Setup

First install [Octave](https://www.gnu.org/software/octave/) and the [symbolic package](https://octave.sourceforge.io/symbolic/) using the website or your package manager of choice.

Then in octave type in the following code

```MATLAB
pkg load symbolic
```
    

## Usage

For every variable not defined earlier in your expression, make sure to declare it as a symbolic data type

```MATLAB
syms x y
```

Then make an expression

```MATLAB
expr = y + sin(x)^2 + cos(x)^2
```

You can then ask Octave to simplify the expression for you

```MATLAB
simp_expr = simplify(expr)
```

Displaying it shows it as

```MATLAB
(sym) y + 1
```

Which is indeed a simplification using a trig identity 🙂

Update: Octave's symbolic is based on [SymPy](https://www.sympy.org/en/index.html). If you're confortable with Python, I recommend checking it out.
