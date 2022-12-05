---
title: "Archiving Sites"
date: 2019-08-02T22:42:16-04:00
draft: false
tags: [ "Archive" ]
---

I have several old Wordpress sites lying around that I would like to archive but not maintain anymore. Since I don't intend to create any more content on these sites, we can use tools like `wget` to scrape an existing site and provide a somewhat *read-only* copy of it. I say read-only not because we can't edit it, but because it's not in the original source format of the website.

There have been several tackles to the problem:

- https://stackoverflow.com/questions/538865/how-do-you-archive-an-entire-website-for-offline-viewing#538878
- [https://letswp.io/download-an-entire-website-wget-windows/](https://web.archive.org/web/20190915143432/https://letswp.io/download-an-entire-website-wget-windows/)

And ultimately after consulting these resources I've came to the following command:

```bash
wget --mirror \
     --convert-links \
     --adjust-extension \
     --no-clobber \
     --page-requisites \
     https://url/of/web/site
```

There were other solutions in that stack overflow post, but something about the simplicity of `wget` appealed to me.

[Example site I archived with this.](https://sentenceworthy.com)
