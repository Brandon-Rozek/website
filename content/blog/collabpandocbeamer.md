---
title: "Collaborating on Beamer Pandoc Slides"
date: 2019-11-22T14:49:19-05:00
draft: false
medium_enabled: true
---

Recently I've been making slides using Pandoc with Beamer. However, I came across the issue where I needed to collaborate with someone using already existing slides written in Markdown.

Sadly, I don't think this person (and most people for that matter) wants to edit slides in Markdown and use Pandoc. So I needed to convert this into another source material. My original plan was to convert this into a Powerpoint and put it into Google Slides. When I went to convert it using Pandoc, it stripped my math typing and theme. Unfortunately, that wasn't going to work for me.

The solution I ultimately ended using was the following.
1. Convert the Markdown into Latex
2. Upload the latex document into Overleaf
3. Use the share feature in Overleaf

