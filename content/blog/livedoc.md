---
title: "Live Documentation"
date: 2019-09-27T23:07:19-04:00
draft: false
tags: ["Documentation"]
medium_enabled: true
---

This blog post is mostly for one of my teams in which I use Jupyter Notebooks for documentation. Perhaps after reading this post, you the reader can understand why it might be beneficial to use Jupyter Notebooks as a form of documentation.

## Why?

So why Jupyter Notebooks?

- Follows the literate programming approach. You can write text explaining a feature and then immediately show code and it's result.
- It's modifiable. If your user wants to play around with the documentation, the environment is set up for them to do so.
- It's exportable. Let's say another user doesn't want to bother setting it up. Well it's super simple to just export the notebook as a PDF and send that to them instead.

## Setting up

Jupyter Notebooks are part of the [Project Jupyter](https://jupyter.org/) suite of products. You can install it via a `pip` package, but it is more commonly installed via the [Anaconda Distribution](https://www.anaconda.com/)

Once you have that installed, run `jupyter lab` in the directory that you wish to execute code from. You might need to be in the `bash` shell for this to work since the installer modifies those environmental variables.