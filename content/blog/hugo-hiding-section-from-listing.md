---
date: 2022-05-19 22:43:04-04:00
draft: false
math: false
medium_enabled: true
medium_post_id: d71625f9235b
tags:
- Hugo
title: Hiding Section From Listing in Hugo
---

In Hugo you can list all the sections using the following code

```html
{{ range .Site.Sections }}
  <li><a href="{{ .Permalink }}">{{ .Title }}</a></li>
{{ end }}
```

However what if there's a section that you want to hide for whatever reason? Let us say that you have a section labeled "unlisted" that you want to hide. The directory structure can look like this:

```
content/
  posts/
  unlisted/
  bookmarks/
// ...
```

There are two types of hidden that I can think of:

- You don't want any pages within unlisted to render at all.
- You want it to render, but not appear in the section listing

For the first case, [Filosophy suggests](https://filosophy.org/code/disabling-a-specific-section-in-hugo/) to rename the section so that it starts with a dot. For example, `.unlisted`.

For the second case, we need to introduce a page variable to help us choose when to display it. Let us call that page variable `hidden`. To set it to true, you need to add it to the frontmatter of `content/unlisted/_index.md`.

```yaml
---
hidden: true
---
```

Then replace the listing code with the following:

```html
{{ range .Site.Sections }}
  {{ if not .Params.hidden }}
    <li><a href="{{ .Permalink }}">{{ .Title }}</a></li>
  {{ end }}
{{ end }}
```