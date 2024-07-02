---
title: "Re: Static+, can it work?"
date: 2024-07-01T21:59:26-07:00
draft: false
tags: []
math: false
medium_enabled: false
---

Gabriel recently released a [blog post](https://gabe.rocks/tech/static-plus/) thinking about the space between a static website and a full-blown CMS.

It's something that I think about semi-often. It's difficult to characterize what `static+` means, because I believe we each have our reasons for using a static site generator. This includes but is not limited to [speed](https://stackoverflow.com/questions/6869210/which-is-faster-mysql-php-or-serving-straight-from-static-files), [security](https://nvd.nist.gov/vuln/search/results?form_type=Basic&results_type=overview&query=wordpress&search_type=all), and my personal reason of [data portability](https://en.wikipedia.org/wiki/Data_portability).

I like how my Hugo website is written in Markdown files. This means that if Hugo stopped development now, I can move to a different static site generator in the future.

With this in mind, what does `static+` mean for me? For data portability, this means that if I want an API to create a blog post ideally it'll:

1) Write the contents of the blog post in the API request to a Markdown file
2) Commit it to my git repository
3) Re-run `hugo` to build the site

I enjoy my writing workflow on my computer, so the idea is crafting some easy way to compose posts on my phone.

Hugo maintains a [list of frontends](https://gohugo.io/tools/front-ends/) which I haven't vetted but may actually satisfy those requirements. Perhaps it's time and energy that's preventing me from [Jamstack'n](https://jamstack.org/) my website. 

Or it could be simplicity that makes me want a simpler solution like a custom API that Gabriel describes.

Or I want a reason to tinker with a custom API :)







