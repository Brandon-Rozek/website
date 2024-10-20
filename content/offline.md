---
title: Offline
description: Your device is offline.
layout: offline
hidden: true
---

Your device is offline. You may have some pages cached for offline viewing,
otherwise please wait for the internet to reconnect to continue browsing.

[Homepage](/)

{{< unsafe >}}

<ul id='offline-posts'></ul>

<script>

function daysAgo(date) {
  date.setHours(0, 0, 0, 0);
  const time = date.getTime();
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

async function listPages() {
  // Get a list of all of the caches for this origin
  const cacheNames = await caches.keys();
  const result = [];

  for (const name of cacheNames) {
    // Open the cache
    if (name.includes('/blog')) {
      const cache = await caches.open(name);

      // Get a list of entries. Each item is a Request object
      for (const request of await cache.keys()) {
        const url = request.url;
        const post = await cache.match(request);
        const body = await post.text();
        const title = body.match(/<title>(.*)<\/title>/)[1];
        result.push({
          url,
          post,
          title,
          visited: new Date(post.headers.get('date')),
        });
        }
      }
  }
  

  const el = document.querySelector('#offline-posts');

  if (result.length) {
    el.innerHTML = result
      .sort((a, b) => {
        return a.published.toJSON() < b.published.toJSON() ? 1 : -1;
      })
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

  return result;
}

document.addEventListener("DOMContentLoaded", (event) => {
  if (navigator && navigator.serviceWorker) {
    listPages()
  }
});
</script>

{{< /unsafe >}}