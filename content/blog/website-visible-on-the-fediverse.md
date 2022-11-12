---
title: "Having your Website Visible on the Fediverse"
date: 2022-06-12T18:35:30-04:00
draft: false
tags: ["Mastodon"]
math: false
---

[ActivityPub](https://www.w3.org/TR/activitypub/) is the backbone
of the [Fediverse](https://en.wikipedia.org/wiki/Fediverse).
Implementing this protocol will allow one to interact with users on
[Mastodon](https://joinmastodon.org/),
[Pixelfed](https://pixelfed.org/),
[Friendica](https://friendi.ca/),
and [others](http://fediverse.party/).
Unfortuately for a static website, this protocol uses a
publish-subscribe pattern. A service would need to be written
in order to handle subscribers, pushing messages of published items,
as well as receiving mentions.
At the current state of my website, I am uninterested in creating
such a service. However, I do wish to document the parts
of the ActivityPub protocol I was able to implement so far
using only a static website.
This post extends off of
[Eugen Rochko's work](https://blog.joinmastodon.org/2018/06/how-to-implement-a-basic-activitypub-server/)
which I encourage you to check out.

## Webfinger

When someone looks up a handle on Mastodon, it performs a Webfinger
lookup. For example if I am looking up the user `brozek@brandonrozek.com`,
then the service will perform a GET request at
`https://brandonrozek.com/.well-known/webfinger?resource=acct:brozek@brandonrozek.com`.

A webfinger request should return the handle of the user (the `subject`) as well as
a link to its `actor`.

```json
{
	"subject": "acct:brozek@brandonrozek.com",

	"links": [
		{
			"rel": "self",
			"type": "application/activity+json",
			"href": "https://brandonrozek.com/brozek.json"
		}
	]
}
```

Now for a static site with one user, you can hardcode the webfinger directly
at `.well-known/webfinger`. The only issue is that many webservers determine the
mimetype of a file by its extension. In this case, we'll have to let the webserver
(mine is nginx) know how to serve it.

```nginx
location /.well-known/webfinger {
    default_type application/jrd+json;
    add_header Access-Control-Allow-Origin "*";
}
```

## Actor

An actor defines how to interact with a user as well as its metadata.
This file also needs to be served with the `application/jrd+json` header.
Below is an example of what I have on my website as well as how it looks
on Mastodon.

```json
{
	"@context": [
		"https://www.w3.org/ns/activitystreams",
		"https://w3id.org/security/v1"
	],
	"id": "https://brandonrozek.com/brozek.json",
	"type": "Person",
	"inbox": "https://brandonrozek.com/inbox",
	"outbox": "https://granary.io/url?input=rss&output=as2&url=http%3A%2F%2Fbrandonrozek.com%2Fblog%2Findex.xml",
	"preferredUsername": "brozek",
	"name": "Brandon Rozek",
	"summary": "<p>Writings from <a href='https://brandonrozek.com'>https://brandonrozek.com</p></a><p>Social profile <a href='https://fosstodon.org/@brozek'>@brozek@fosstodon.org</a></p>",
	"url": "https://brandonrozek.com",
	"manuallyApprovesFollowers": false,
	"discoverable": true,
	"published": "2022-05-17T00:00:00Z",
	"icon": {
		"type": "Image",
		"mediaType": "image/jpeg",
		"url": "https://brandonrozek.com/img/avatar.jpg"
	},
	"publicKey": {
		"id": "https://brandonrozek.com/brozek.json#main-key",
		"owner": "https://brandonrozek.com.com/brozek.json",
		"publicKeyPem": "-----BEGIN PUBLIC KEY-----...-----END PUBLIC KEY-----"
	}
}
```

![Screenshot of brozek@brandonrozek.com profile on Mastodon](/files/images/blog/202206121902.png)

## Limitations and Conclusion

Notice in the previous screenshot that it says "Cancel Follow Request".
This is because my static website is not equipped to handle a follow request.
Standard ActivityPub servers keep an inventory of all the users that follow
their users and who each user on the server is following.

The outbox defines items that the user has published.
I have it pointed to an activity JSON feed generated directly
from my RSS using granary.io.
Mastodon correctly displays the number of blog posts I have,
but sadly it does not show any of them. I'm not entirely
sure why, though my hypothesis is that the posts need to be pushed
to the Mastodon server when its created. It could also be that the
actor isn't defined properly in the activity JSON feed. If you happen
to know please get in touch.
