---
title: "Blog Workflow"
date: 2019-10-28T00:16:44-04:00
draft: false
tags: ["Hugo", "Blogging"]
medium_enabled: true
---

You may be curious on how I create content for this blog. There's pros and cons to my approach. One pro is that it's relatively easy for me to crank something out and upload it to my site. The downside is that it's not as easily customizable.



I use Hugo as my static site generator. It works with Markdown files. I begin every blog post by typing

```bash
hugo new blog/title.md
```

This creates a file called `title.md` in `content/blog` with front-matter yaml information such as the title and the datetime that I created the post.

I then use my favorite Markdown editor `typora` to open up the file in the background.

```bash
typora content/blog/title.md &
```

Write some great words down, compile the website, then sync it to my site!

```bash
hugo
rsync -Paz --delete public/ brandonrozek.com:/path/to/site/folder
```

