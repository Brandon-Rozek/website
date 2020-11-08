---
title: "Preserving Classic URLs on my Website"
date: 2020-10-28T21:06:57-04:00
draft: false
tags: []
---

At some point in 2018 I switched my website from using Wordpress on the backend to Hugo. I used a simple script to migrate everything over and in that migration a few things broke.

- Code snippets do not show up
- Images don't show up
- URLs are different

I've gone back through some of my old posts and fixed up the code snippets. I usually decide to go back when I see sufficient traffic to one of those older pages.

I recently discovered that Hugo supported [aliases](https://gohugo.io/content-management/urls/#aliases). This will allow me to setup redirect at the old URLs that my blog posts used to be in. I can do this by adding a small snippet to my front YAML.

```yaml
aliases:
    - /2018/06/05/old/url/here
```

This will then redirect `https://brandonrozek.com/2018/06/05/old/url/here` to the current URL of the post I'm editing.

When I discovered this, I went ahead and redirected all my old URL blog posts to their current day versions. It makes me happy that I'm lowering the amount of link rot that I'm contributing to the web.

How does it do this? It creates a simple webpage that contains a HTTP-Equiv tag which tells the browser to redirect it. Directly from the Hugo documentation:

```html
<!DOCTYPE html>
<html>
  <head>
    <title>https://example.com/posts/my-intended-url</title>
    <link rel="canonical" href="https://example.com/posts/my-intended-url"/>
    <meta name="robots" content="noindex">
    <meta http-equiv="content-type" content="text/html; charset=utf-8"/>
    <meta http-equiv="refresh" content="0; url=https://example.com/posts/my-intended-url"/>
  </head>
</html>
```

