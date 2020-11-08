---
id: 449
title: Limiting the Cache in Service Workers Revisited
date: 2015-11-30T00:34:15+00:00
author: Brandon Rozek
layout: post
guid: https://brandonrozek.com/?p=449
aliases:
    - /2015/11/limiting-cache-service-workers-revisited/
    - /2015/11/limiting-cache-service-workers-revisited1/
    - /2015/11/limiting-cache-service-workers-revisited2/
    - /2015/11/limiting-cache-service-workers-revisited3/
permalink: /2015/11/limiting-cache-service-workers-revisited3/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"9cc502aae12e";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:93:"https://medium.com/@brandonrozek/limiting-the-cache-in-service-workers-revisited-9cc502aae12e";}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"9cc502aae12e";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:93:"https://medium.com/@brandonrozek/limiting-the-cache-in-service-workers-revisited-9cc502aae12e";}'
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
tumblr_post_id:
  - "135657767639"
  - "135657767639"
tumblr_crosspostr_crosspost:
  - 'N'
kind:
  - article
---
Summary: I rewrote how cache limiting works to address a few problems listed later in this post. Check out the [gist](https://gist.github.com/brandonrozek/0cf038df40a913fda655) for the updated code.

<!--more-->

I wrote a function in my [previous service worker post](https://brandonrozek.com/2015/11/service-workers/) to help limit the cache. Here&#8217;s a reminder of what it looked like.

```javascript
var limitCache = function(cache, maxItems) {
	cache.keys().then(function(items) {
		if (items.length &gt; maxItems) {
			cache.delete(items[0]);
		}
	})
}
```

### The Problem

Jeremy Keith updated the service worker on his site and noticed that the images has blown past the amount he allocated for it ([post](https://adactio.com/journal/9844)). Looking back at my service worker, I noticed that mine has the same shortcoming as well. So what happened? Service workers function in an asynchronous manner. Meaning it can be processing not just one, but many fetch events at the same time. This comes into conflict when there are synchronous instructions such as deleting the first item from the cache which Jeremy describes in his follow up [post](https://adactio.com/journal/9888).

### A Solution

Jeremy wrote a function to help trim the cache and asked when it would be appropriate to apply it.

```javascript
var trimCache = function (cacheName, maxItems) {
    caches.open(cacheName)
        .then(function (cache) {
            cache.keys()
                .then(function (keys) {
                    if (keys.length &gt; maxItems) {
                        cache.delete(keys[0])
                            .then(trimCache(cacheName, maxItems));
                    }
                });
        });
};
```

And that got me thinking. In what situations is this problem more likely to occur? This particular problem happens when a lot of files are being called asynchronously. This problem doesn&#8217;t occur when only one file is being loaded. So when do we load a bunch of files? During page load. During page load, the browser might request css, javascript, images, etc. Which for most [websites](http://royal.pingdom.com/2011/11/21/web-pages-getting-bloated-here-is-why/), is a lot of files. Let&#8217;s now move our focus back to the humble script.js. Before, the only role it played with service workers was registering the script. However, if we can get the script to notify the service worker when the page is done loading, then the service worker will know when to trim the cache.

```javascript
if ('serviceWorker' in navigator) {
	navigator.serviceWorker.register('https://yourwebsite.com/serviceworker.js', {scope: '/'});
}
window.addEventListener("load", function() {
	if (navigator.serviceWorker.controller != null) {
		navigator.serviceWorker.controller.postMessage({"command":"trimCache"});
	}
});
```

Why `if (navigator.serviceWorker.controller != null)` Service Workers don&#8217;t take control of the page immediately but on subsequent page loads, Jake Archibald [explains](https://jakearchibald.com/2014/using-serviceworker-today/). When the service worker does have control of the page however, we can use the [postMessage api](https://developer.mozilla.org/en-US/docs/Web/API/Worker/postMessage) to send a message to the service worker. Inside, I provided a json with a &#8220;command&#8221; to &#8220;trimCache&#8221;. Since we send the json to the service worker, we need to make sure that it can receive it.

```javascript
self.addEventListener("message", function(event) {
	var data = event.data;

	if (data.command == "trimCache") {
		trimCache(version + "pages", 25);
		trimCache(version + "images", 10);
		trimCache(version + "assets", 30);
	}
});
```

Once it receives the command, it goes on to trim all of the caches.

### Conclusion

So whenever you download a bunch of files, make sure to run <code class="language-javascript">navigator.serviceWorker.controller.postMessage({"command":"trimCache"});</code> on the main javascript file to trim the cache. A downside to this method is that since Service Workers don&#8217;t take control during the first page load, the cache isn&#8217;t trimmed until the second page load. If you can find a way to make it so that this event happens in the first page load [tell me](mailto:hello@brandonrozek.com) about it/write a blog post. 🙂 **Update:** To get the service worker to take control of the page immediately call [self.skipWaiting()](https://developer.mozilla.org/en-US/docs/Web/API/ServiceWorkerGlobalScope/skipWaiting) after the install event and [self.clients.claim()](https://developer.mozilla.org/en-US/docs/Web/API/Clients/claim) after the activate event. Current code for our humble service worker:

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
	trims the cache
	If cache has more than maxItems then it removes the excess items starting from the beginning
*/
var trimCache = function (cacheName, maxItems) {
    caches.open(cacheName)
        .then(function (cache) {
            cache.keys()
                .then(function (keys) {
                    if (keys.length &gt; maxItems) {
                        cache.delete(keys[0])
                            .then(trimCache(cacheName, maxItems));
                    }
                });
        });
};


//When the service worker is first added to a computer
self.addEventListener("install", function(event) {
	event.waitUntil(updateStaticCache()
				.then(function() { 
					return self.skipWaiting(); 
				})
			);
})

self.addEventListener("message", function(event) {
	var data = event.data;
	
	//Send this command whenever many files are downloaded (ex: a page load)
	if (data.command == "trimCache") {
		trimCache(version + "pages", 25);
		trimCache(version + "images", 10);
		trimCache(version + "assets", 30);
	}
});

//Service worker handles networking
self.addEventListener("fetch", function(event) {

	//Fetch from network and cache
	var fetchFromNetwork = function(response) {
		var cacheCopy = response.clone();
		if (event.request.headers.get('Accept').indexOf('text/html') != -1) {
			caches.open(version + 'pages').then(function(cache) {
				cache.put(event.request, cacheCopy);
			});
		} else if (event.request.headers.get('Accept').indexOf('image') != -1) {
			caches.open(version + 'images').then(function(cache) {
				cache.put(event.request, cacheCopy);
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
			return new Response('Offlineoffline', { headers: { 'Content-Type': 'image/svg+xml' }});
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
	event.waitUntil(clearOldCaches()
				.then(function() { 
					return self.clients.claim(); 
				})
			);
});
```

```javascript
if ('serviceWorker' in navigator) {
	navigator.serviceWorker.register('https://brandonrozek.com/serviceworker.js', {scope: '/'});
}
window.addEventListener("load", function() {
	if (navigator.serviceWorker.controller != null) {
		navigator.serviceWorker.controller.postMessage({"command":"trimCache"});
	}
});
```