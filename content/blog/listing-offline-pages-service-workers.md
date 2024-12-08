---
title: "Listing Offline Pages with Service Workers"
date: 2024-12-07T10:05:20-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

Using web service workers, you can set it up so that visitors [have an offline experience](/blog/2015-11-14-service-workers/) with your website. In my original blog post, I wrote about how to cache pages, and how to show them when the visitor lacks an Internet connection, or a special [offline page](/offline) instead.

This, however, doesn't list what pages are cached on their device. Wouldn't it make sense to show this in the offline page?  It was kinda crazy that I didn't do this before, so in this post we'll go over how to showcase the list of saved offline pages.

---

Recall that web workers give us access to the [cache interface](https://developer.mozilla.org/en-US/docs/Web/API/Cache). From it, we can access any number of caches.

```javascript
const cache = await caches.open('v1::website')
```

A cache is a dictionary, with `Requests` objects mapped to `Response` objects. We can filter within our cache for request-response pairs that match a particular URL structure or has a certain content type.

```javascript
for (const request of await cache.keys()) {
    const url = request.url;
    if (url.includes('/blog')) {
        const response = await cache.match(request)
        if (response.headers.get('content-type').includes('text/html')) {
            process(request, response);
        }
    }
}
```

For my offline pages listing, I want it to look like the following:

- [Monitoring my Hard Drives with SMART Attributes](/blog/monitoring-disks-smartattributes/) (visited 20 days ago)
- [Adventures in Bird Watching](/blog/adventures-in-bird-watching) (visited 40 days ago)

We can get the title by searching for the `<title>` tag within the response object.

```javascript
const body = response.text()
const title = body.match(/<title>(.*)<\/title>/)[1]
```

For the last visited, we can look at the response headers.

```javascript
const visited = new Date(post.headers.get('date'))
```

Let's say we stored all of this within a list

```javascript
result.push({url, title, visited})
```

We can then iterate over `result` and add list items within a unordered-list `<ul>`.

```javascript
const el = document.querySelector('#offline-posts');
if (result.length) {
	el.innerHTML = result
      .map((res) => {
        let html = `<li>
        <a href="${res.url}">${res.title}</a>
        <small><span title="${res.visited.toString()}">
            (visited ${daysAgo(res.visited)})
        </span></small>
        </li>`;
        return html;
      })
      .join('\n');
}
```

The function `daysAgo` returns an easy to read time delta between the visited timestamp and now.

```javascript
function daysAgo(date) {
  date.setHours(0, 0, 0, 0);
  const time = date.getTime();
  const today = new Date();
  today.setHours(0, 0, 0, 0);
  const now = today.getTime();
  const delta = ((now - time) / 1000 / 60 / 60 / 24) | 0;

  if (delta < 1) {
    return 'today';
  }

  if (delta === 1) {
    return 'yesterday';
  }

  return `${delta | 0} days ago`;
}
```



