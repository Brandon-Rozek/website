---
id: 400
title: An Offline Experience with Service Workers
date: 2015-11-14T15:47:06+00:00
author: Brandon Rozek
aliases:
    - /2015/11/service-workers/
permalink: /2015/11/service-workers/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"125e50979ed8";s:21:"follower_notification";s:3:"yes";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:88:"https://medium.com/@brandonrozek/an-offline-experience-with-service-workers-125e50979ed8";}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"125e50979ed8";s:21:"follower_notification";s:3:"yes";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:88:"https://medium.com/@brandonrozek/an-offline-experience-with-service-workers-125e50979ed8";}'
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
tags: ["Web", "JS"]
---
I’m excited to say that I’ve written my first service worker for brandonrozek.com. What is a service worker? A service worker provides an extra layer between the client and the server. The exciting part about this is that you can use service workers to deliver an offline experience. (Cached versions of your site, offline pages, etc.)

<!--more-->

Service workers are currently supported in Chrome, Opera, and Firefox nightly. You don’t have to worry too much about browser support because the Service Worker spec was written in a [progressively enchanced](http://alistapart.com/article/understandingprogressiveenhancement) way meaning it won’t break your existing site 🙂

# Caveats

You need HTTPS to be able to use service workers on your site. This is mainly for security reasons. Imagine if a third party can control all of the networking requests on your site? If you don’t want to go out and buy a SSL Certificate, there are a couple free ways to go about this.
1. [Cloudflare](https://www.cloudflare.com/)
2. [Let’s Encrypt](https://letsencrypt.org/) 


Service workers are promise heavy. Promises contain a then clause which runs code asynchronously. If you’re not accustomed to this idea please check out this [post](https://ponyfoo.com/articles/es6-promises-in-depth) by Nicolas Bevacqua. Now onto making the service worker! If you want to skip to the final code scroll down to the bottom. If you don’t like my syntax highlighting, then you can check out this [gist](https://gist.github.com/brandonrozek/0cf038df40a913fda655).

# Register the service worker

Place `service-worker.js` on the root of your site. This is so the service worker can access all the files in the site. Then in your main javascript file, register the service worker.

```javascript
if (navigator.serviceWorker) {
  navigator.serviceWorker.register('/serviceworker.js', {
    scope: '/'
  });
}
```


# Install the service worker

The first time the service worker runs, it emits the `install` event. At this time, we can load the visitor’s cache with some resources for when they’re offline. Every so often, I like to change up the theme of the site. So I have version numbers attached to my files. I would also like to invalidate my cache with this version number. So at the top of the file I added

```javascript
var version = 'v2.0.24:';
```


Now, to specify which files I want the service worker to cache for offline use. I thought my home page and my offline page would be good enough.

```javascript
var offlineFundamentals = [
    '/',
    '/offline/'
];
```


Since <code class="language-javascript">cache.addAll()</code> hasn’t been implemented yet in any of the browsers, and the polyfill implementation didn’t work for my needs. I pieced together my own.

```javascript
var updateStaticCache = function() {
    return caches.open(version + 'fundamentals').then(function(cache) {
        return Promise.all(offlineFundamentals.map(function(value) {
            var request = new Request(value);
            var url = new URL(request.url);
            if (url.origin != location.origin) {
                request = new Request(value, {mode: 'no-cors'});
            }
            return fetch(request).then(function(response) {
                var cachedCopy = response.clone();
                return cache.put(request, cachedCopy);
            });
        }))
    })
};
```


Let’s go through this chunk of code.

  1. Open the cache called <code class="language-javascript">'v2.0.24:fundamentals'</code>
  2. Go through all of the <code class="language-javascript">offlineFundamental</code>‘s URLs 
      * Does the file I ask for come from the same domain as my site?
      * No. Then, make the request ‘no-cors’ (I had difficulty getting my asset files in cors mode. If the cors headers are included in the response, then you can take out this line)
      * Fetch the file from the network and then cache it.

Now we call it when the `install` event is fired.

```javascript
self.addEventListener("install", function(event) {
    event.waitUntil(updateStaticCache())
})
```


With this we now cached all the files in the offlineFundamentals array during the install step.

# Clear out the old cache

Since we’re caching everything. If you change one of the files, your visitor wouldn’t get the changed file. Wouldn’t it be nice to remove old files from the visitor’s cache? Every time the service worker finishes the install step, it releases an `activate` event. We can use this to look and see if there are any old cache containers on the visitor’s computer. From [Nicolas’ code](https://ponyfoo.com/articles/serviceworker-revolution). Thanks for sharing 🙂

```javascript
var clearOldCaches = function() {
    return caches.keys().then(function(keys) {
            return Promise.all(
                      keys
                        .filter(function (key) {
                              return key.indexOf(version) != 0;
                        })
                        .map(function (key) {
                              return caches.delete(key);
                        })
                );
        })
}
```


  1. Check the names of each of the cache containers
  2. If they don’t start with the correct version number 
      * Delete that cache container

Call the function when the `activate` event fires.

```javascript
self.addEventListener("activate", function(event) {
    event.waitUntil(clearOldCaches())
});
```


# Intercepting fetch requests 

The cool thing about service worker’s is that it can handle file requests. We could cache all files requested for offline use, and if a fetch for a resource failed, then the service worker can look for it in the cache or provide an alternative. This is a large section, so I’m going to attempt to break it down as much as I can.

## Limit the cache {#limit-the-cache}

If the visitor started browsing all of the pages on my site, his or her cache would start to get bloated with files. To not burden my visitors, I decided to only keep the latest 25 pages and latest 10 images in the cache.

```javascript
var limitCache = function(cache, maxItems) {
    cache.keys().then(function(items) {
        if (items.length > maxItems) {
            cache.delete(items[0]);
        }
    })
}
```


We’ll call it later in the code.

## Fetch from network and cache

Every time I fetch a file from the network I throw it into a specific cache container. <code class="language-javascript">'pages'</code> for HTML files, <code class="language-javascript">'images'</code> for CSS files, and <code class="language-javascript">'assets'</code> for any other file. This is so I can handle the cache limiting above easier. Defined within the `fetch` event.

```javascript
var fetchFromNetwork = function(response) {
        var cacheCopy = response.clone();
        if (event.request.headers.get('Accept').indexOf('text/html') != -1) {
            caches.open(version + 'pages').then(function(cache) {
                cache.put(event.request, cacheCopy).then(function() {
                    limitCache(cache, 25);
                })
            });
        } else if (event.request.headers.get('Accept').indexOf('image') != -1) {
            caches.open(version + 'images').then(function(cache) {
                cache.put(event.request, cacheCopy).then(function() {
                    limitCache(cache, 10); 
                });
            });
        } else {
            caches.open(version + 'assets').then(function add(cache) {
                cache.put(event.request, cacheCopy);
            });
        }
        return response;
    }
```

## When the network fails

There are going to be times where the visitor cannot access the website. Maybe they went in a tunnel while they were riding a train? Or maybe your site went down. I thought it would be nice for my reader’s to be able to look over my blog posts again regardless of an internet connection. So I provide a fall-back. Defined within the `fetch` event.

```javascript
var fallback = function() {
        if (event.request.headers.get('Accept').indexOf('text/html') != -1) {
            return caches.match(event.request).then(function (response) { 
                return response || caches.match('/offline/');
            })
        } else if (event.request.headers.get('Accept').indexOf('image') != -1) {
            return new Response('&lt;svg width="400" height="300" role="img" aria-labelledby="offline-title" viewBox="0 0 400 300" xmlns="http://www.w3.org/2000/svg"&gt;&lt;title id="offline-title"&gt;Offline&lt;/title&gt;&lt;g fill="none" fill-rule="evenodd"&gt;&lt;path fill="#D8D8D8" d="M0 0h400v300H0z"/&gt;&lt;text fill="#9B9B9B" font-family="Helvetica Neue,Arial,Helvetica,sans-serif" font-size="72" font-weight="bold"&gt;&lt;tspan x="93" y="172"&gt;offline&lt;/tspan&gt;&lt;/text&gt;&lt;/g&gt;&lt;/svg&gt;', { headers: { 'Content-Type': 'image/svg+xml' }});
        } 
    }
```


  1. Is the request for a HTML file? 
      * Show the [offline](https://brandonrozek.com/offline/) page.
  2. Is the request for an image? 
      * Show a place-holder image (Courtesy of [Jeremy Keith](https://adactio.com/journal/9775))

## Handle the request

First off, I’m only handling GET requests.

```javascript
if (event.request.method != 'GET') {
        return;
}
```


For HTML files, grab the file from the network. If that fails, then look for it in the cache. _Network then cache strategy_ 

```javascript
if (event.request.headers.get('Accept').indexOf('text/html') != -1) {
            event.respondWith(fetch(event.request).then(fetchFromNetwork, fallback));
        return;
        }
```


For non-HTML files, follow this series of steps

  1. Check the cache
  2. Does a cache exist for this file? 
      * Yes. Then show it
      * No. Then grab it from the network and cache it.

_Cache then network strategy_ 

```javascript
event.respondWith(
        caches.match(event.request).then(function(cached) {
            return cached || fetch(event.request).then(fetchFromNetwork, fallback);
        })
    )
```


For different stategy’s, take a look at Jake Archibald’s [offline cookbook](https://jakearchibald.com/2014/offline-cookbook/).

# Conclusion

With all of that, we now have a fully functioning offline-capable website! I wouldn’t be able to implement this myself if it wasn’t for some of the awesome people I mentioned earlier sharing their experience. So share, share, share! With that sentiment, I’ll now share the full code for `service-worker.js` **Update:** There is a new version of this code over at this [blog post](https://brandonrozek.com/2015/11/limiting-cache-service-workers-revisited/).

```javascript
var version = 'v2.0.24:';

var offlineFundamentals = [
    '/',
    '/offline/'
];

//Add core website files to cache during serviceworker installation
var updateStaticCache = function() {
    return caches.open(version + 'fundamentals').then(function(cache) {
        return Promise.all(offlineFundamentals.map(function(value) {
            var request = new Request(value);
            var url = new URL(request.url);
            if (url.origin != location.origin) {
                request = new Request(value, {mode: 'no-cors'});
            }
            return fetch(request).then(function(response) {
                var cachedCopy = response.clone();
                return cache.put(request, cachedCopy);
            });
        }))
    })
};

//Clear caches with a different version number
var clearOldCaches = function() {
    return caches.keys().then(function(keys) {
            return Promise.all(
                      keys
                        .filter(function (key) {
                              return key.indexOf(version) != 0;
                        })
                        .map(function (key) {
                              return caches.delete(key);
                        })
                );
        })
}

/*
    limits the cache
    If cache has more than maxItems then it removes the first item in the cache
*/
var limitCache = function(cache, maxItems) {
    cache.keys().then(function(items) {
        if (items.length > maxItems) {
            cache.delete(items[0]);
        }
    })
}


//When the service worker is first added to a computer
self.addEventListener("install", function(event) {
    event.waitUntil(updateStaticCache())
})

//Service worker handles networking
self.addEventListener("fetch", function(event) {

    //Fetch from network and cache
    var fetchFromNetwork = function(response) {
        var cacheCopy = response.clone();
        if (event.request.headers.get('Accept').indexOf('text/html') != -1) {
            caches.open(version + 'pages').then(function(cache) {
                cache.put(event.request, cacheCopy).then(function() {
                    limitCache(cache, 25);
                })
            });
        } else if (event.request.headers.get('Accept').indexOf('image') != -1) {
            caches.open(version + 'images').then(function(cache) {
                cache.put(event.request, cacheCopy).then(function() {
                    limitCache(cache, 10);
                });
            });
        } else {
            caches.open(version + 'assets').then(function add(cache) {
                cache.put(event.request, cacheCopy);
            });
        }
    
        return response;
    }
    
    //Fetch from network failed
    var fallback = function() {
        if (event.request.headers.get('Accept').indexOf('text/html') != -1) {
            return caches.match(event.request).then(function (response) { 
                return response || caches.match('/offline/');
            })
        } else if (event.request.headers.get('Accept').indexOf('image') != -1) {
            return new Response('&lt;svg width="400" height="300" role="img" aria-labelledby="offline-title" viewBox="0 0 400 300" xmlns="http://www.w3.org/2000/svg"&gt;&lt;title id="offline-title"&gt;Offline&lt;/title&gt;&lt;g fill="none" fill-rule="evenodd"&gt;&lt;path fill="#D8D8D8" d="M0 0h400v300H0z"/&gt;&lt;text fill="#9B9B9B" font-family="Helvetica Neue,Arial,Helvetica,sans-serif" font-size="72" font-weight="bold"&gt;&lt;tspan x="93" y="172"&gt;offline&lt;/tspan&gt;&lt;/text&gt;&lt;/g&gt;&lt;/svg&gt;', { headers: { 'Content-Type': 'image/svg+xml' }});
        }
    }
    
    //This service worker won't touch non-get requests
    if (event.request.method != 'GET') {
        return;
    }
    
    //For HTML requests, look for file in network, then cache if network fails.
    if (event.request.headers.get('Accept').indexOf('text/html') != -1) {
            event.respondWith(fetch(event.request).then(fetchFromNetwork, fallback));
        return;
        }
    
    //For non-HTML requests, look for file in cache, then network if no cache exists.
    event.respondWith(
        caches.match(event.request).then(function(cached) {
            return cached || fetch(event.request).then(fetchFromNetwork, fallback);
        })
    )
});

//After the install event
self.addEventListener("activate", function(event) {
    event.waitUntil(clearOldCaches())
});
```