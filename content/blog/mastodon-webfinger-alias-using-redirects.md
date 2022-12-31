---
title: "Mastodon/Webfinger Alias using HTTP Redirects"
date: 2022-12-31T09:50:00-05:00
draft: false
tags: ["Mastodon"]
math: false
---

Mastodon uses the Webfinger protocol to find users. For example, if you search for `@brozek@brandonrozek.com` it will access the url:

```
https://brandonrozek.com/.well-known/webfinger?resource=acct:brozek@brandonrozek.com
```

As of the time of writing, I do not have a strong interest in running my own Mastodon server. I instead am active on `@brozek@fosstodon.org`

```
https://fosstodon.org/.well-known/webfinger?resource=acct:brozek@fosstodon.org
```

If you try to access the last URL in your web browser, you'll notice that it doesn't return anything. This is because the server will only respond if we specify the content type. In `curl`, we can specify that through the following:

```bash
curl -H 'Accept: application/jrd+json' \
	https://fosstodon.org/.well-known/webfinger?resource=acct:brozek@fosstodon.org
```

Currently, it returns the following

```json
{
  "subject": "acct:brozek@fosstodon.org",
  "aliases": [
    "https://fosstodon.org/@brozek",
    "https://fosstodon.org/users/brozek"
  ],
  "links": [
    {
      "rel": "http://webfinger.net/rel/profile-page",
      "type": "text/html",
      "href": "https://fosstodon.org/@brozek"
    },
    {
      "rel": "self",
      "type": "application/activity+json",
      "href": "https://fosstodon.org/users/brozek"
    },
    {
      "rel": "http://ostatus.org/schema/1.0/subscribe",
      "template": "https://fosstodon.org/authorize_interaction?uri={uri}"
    }
  ]
}
```

Some people have been copy pasting the contents of this file, onto their webserver. However, this makes it so that we can't have multiple aliases on this domain. Instead, we can use our webserver (mine is `nginx`) to redirect the user when the specified handle is requested.

```nginx
location /.well-known/webfinger {
    default_type application/jrd+json;
    add_header Access-Control-Allow-Origin "*";
    if ($arg_resource = acct:brozek@brandonrozek.com) {
        return 301 $scheme://fosstodon.org/.well-known/webfinger?resource=acct:brozek@fosstodon.org;
    }
}
```

Now this isn't a perfect alias, you can't reference `@brozek@brandonrozek.com` and have me be notified. Instead, this only works in user discovery.
