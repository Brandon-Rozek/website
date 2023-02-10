---
date: 2022-05-19 21:24:52-04:00
draft: false
math: false
medium_enabled: true
medium_post_id: b339b9d9793b
tags:
- Documentation
title: Document Formats and Plaintext
---

Microsoft Word, Apple Pages, Google Docs, Libreoffice Writer all provide a method of writing and formatting text. This is then normally stored in a "binary" file. I put binary in quotes as they are often stored in a zip archive of XML files. However, because it's in a zip archive, I cannot use standard plaintext tools to search within the document. 

When would I need to search multiple files at once for a word? Well not only is this useful for programming to find usages of a function, I often use it to find out if I have written about a topic before.

```bash
grep -R chocolate
```

The command above returns the lines of files that contain the word "chocolate". As of the time of writing, I had no such occurrence in my blog directory. Until now, mwahaha.

What's the solution then? To write everything in `.txt` files? Kind of actually. We'll write plaintext files but also include a bit of formatting. We can then *publish* the document by converting it to a webpage (HTML) or a PDF document. The most popular formatting technique is [Markdown](https://daringfireball.net/projects/markdown/) (often has the extension `.md`). That's also the format that my blog posts are encoded in.

One critique of Markdown is that the user does not have much control on the output presentation of the document. Tools like [Pandoc](https://pandoc.org/) allow for custom stylesheets to control it a bit but it's still limited. In my view, the most powerful plaintext document format is [LaTex](https://www.latex-project.org/). Though it's not the simplest to learn. 

If you switch to a plaintext editor like notepad, vscode, vim, etc. it might not come with built in spell check. Luckily on linux, there's a helpful spell check program.

```bash
aspell check filetocheck.md
```

So what plaintext formats do I currently use on a day-to-day?

- Blog posts: Markdown
- Notes: Markdown or random scribbles on physical pieces of paper
- Academic papers: LaTex
- Presentations: LaTex (unless they need video)

If you're interested in learning how to work with plaintext and other cool things, check out the [Plain Text Project](https://plaintextproject.online/) by [Scott Nesbitt](https://scottnesbitt.net/).