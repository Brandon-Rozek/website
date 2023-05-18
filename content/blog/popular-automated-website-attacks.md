---
title: "Top 7 Attacks to My Website"
date: 2023-05-17T23:19:22-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

Running a public server on the Internet means that it's bound to get attacked by automated scripts. Since I [run analytics on my website](https://brandonrozek.com/blog/goaccess/), I'm able to see 404s. In other words, this list constitutes the top requests to my website that fail. 

1. `/wp-login.php`

This is the login page of a Wordpress website. Since this blog engine powers 43% of the Internet, it's not surprising that this is a common target. Sadly for the bots, I don't run this website using Wordpress.

2. `xmlrpc.php`

This one I haven't heard of before until looking it up. I know XML is a data format, and RPC means remote procedure call, but what is the attacker trying to exploit? [Again it's Wordpress](https://codex.wordpress.org/XML-RPC_Support). It seems that this is some API gateway that Wordpress provides to connect with mobile devices, provide pingbacks, and others.

3. `/api/v1/instance`

Through the power of search this seems to be a [API call to Mastodon](https://docs.joinmastodon.org/methods/instance/#v1)! This specifically grabs generic information about the instance such as the number of users, number of statuses, restrictions, etc. I've considered at some point running a Mastodon instance, but maybe it's better to leave it to the pros :)

4. `/.env`

It seems that the Javascript community likes using a `.env` file to keep environmental variables that hold the secrets of your application. Yikes! Make sure that you're blocking this if you have it!

5. `/inbox`

Given #3, I feel like this is ActivityPub related. Though looking at how the [actors are usually structured](https://www.w3.org/TR/activitypub/) it's generally `/username/inbox`. Maybe it's related to email servers instead? I'm unsure.

6. `/status.php`

I'm don't know what this is. Doesn't seem to be Wordpress related. Maybe the attacker is hoping to get the output of `phpinfo()` in those "getting started with PHP" tutorials?

7. `/.git/config`

I can see a situation where someone has a git repository of their website on the server itself and they push to it. Personally, I rsync the generated HTML files. Generally the config will contain the URLs of remote repositories and other settings. Not entirely sure what's sensitive, but maybe someone can let me know.

---

There you have it! The top automated attacks made to my website. If you have any additional information on any of these URL patterns please get in touch. I am curious what these bots are trying to do with the response of each of these queries.
