---
date: 2022-05-15 18:36:16-04:00
draft: false
math: false
medium_enabled: true
medium_post_id: 56667e2c305
tags:
- Mastodon
title: Why I PESOS From Mastodon
---

The [IndieWeb movement](https://indieweb.org) is focused on people controlling their own experience on the web. They accomplish this by encouraging everyone to have their own personal website. Followers can then either subscribe to the [RSS feed](https://aboutfeeds.com/) and provide [Webmentions](https://indieweb.org/Webmention) back to the post, or they can interact with the material directly on another website like [Mastodon](https://joinmastodon.org/). 

The recommended syndicate or copy content is through a technique called [Publish Own Site Syndicate Elsewhere (POSSE)](https://indieweb.org/POSSE). First the author posts on their own website, and then a function takes that post and publishes it on another website. 

However, this is not what I am currently doing to [show my Mastodon toots](/toots). Instead I have implemented [Publish Elsewhere Syndicate Own Site (PESOS)](https://indieweb.org/PESOS). In this model, I first publish directly on Mastodon and then have a function query the Mastodon server to update my personal website. 

## Advantages to PESOS

The main advantage of PESOS is that my primary interaction with Mastodon is through their web and Android app Tusky. Interacting the same way as others on the platform gives me a stronger sense of community when using Mastodon. I don't feel as if I am only just copying posts from my site onto Mastodon. There are also many features built in when posting on Mastodon that I would have to design for and replicate otherwise:

- Content warnings
- Replies
- Boosts
- Character Limits
- Alt Description in Images
- Post Permissions

## Disadvantages to PESOS

The primary way that people are following me is within Mastodon itself as opposed to the RSS feed on my website. This means that if the Mastodon server ever abruptly goes down, then I will lose contact with all of my followers. Mastodon, however, does have some protection against this as a federated network.  Mainly the ability to [move your profile](https://docs.joinmastodon.org/user/moving/) from one Mastodon instance to another.  This gives me a more secure feeling that Mastodon itself won't shut down in the near future.