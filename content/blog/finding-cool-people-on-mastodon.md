---
title: "Finding Cool People on Mastodon"
date: 2022-05-15T20:39:35-04:00
draft: false
tags: []
math: false
---

Mastodon is a cool federated micro-blogging platform that can serve as an alternative to Twitter. One of its primary features is that it shows what they call toots from only people you follow in reverse-chronological order. Nowadays, large tech companies employ recommendation engines to surface content from users (you don't even need to follow) in a non-chronological order driven by the number of interactions users similar to you had with the content. The lack of recommendation engine in Mastodon can be a blessing as low-quality emotional content tends to drive more interactions. However, this can also be a curse as cool new people don't naturally surface in your feed. The following are the techniques I employ to consistently seek out cool new people:

- [Local Feed](#local-feed)
- [Expert Mode](#expert-mode)
- [\#Introduction and \#Introductions](#introduction-and-introductions)
- [FediFollows](#fedifollows)
- [Trunks](#trunks) 
- [Fediverse.Info](#fediverseinfo)

## Local Feed

The easiest and lowest effort way to find new people is to check out what's getting tooted in your local homeserver. These homeservers are often communities within themselves and finding a good fit will help with your initial experience with Mastodon.

To get a feel for how the community within a homeserver is like, you can check their public feed by appending `/public` at the end of the server URL. For example: https://fosstodon.org/public.

Here are some homeservers which I think have great communities and are friendly. This is by no means a complete list:

- [Fosstodon.org](https://fosstodon.org) (Free and Open Source Software Crowd)
- [Mastodon.art](https://mastodon.art) (Art community)
- [Mastodon.radio](https://mastodon.radio) (Amateur Radio Community)

For a more complete list checkout https://instances.social.

If you've already created an account, but want to move to a different homeserver. There's a [guide to moving accounts available on the wiki](https://docs.joinmastodon.org/user/moving/). This process luckily preserves your followers and follows.

## Expert Mode

When you first create an account on Mastodon you will have an interface similar to this following.

![](/files/images/202205151932.png)

One thing you'll notice immediately is that it's very limited. You can only view one feed at a time, and you can't set an option to see your feed and multiple tags in one place. This is where the advanced interface comes in. Go to Preferences -> Appearence -> Check "Enable Advanced Web Interface"

This will then enable something similar to below:

![](/files/images/202205151934.png)

Note the ordering of the feeds I have pinned:

- Home feed
- Tags I am interested in
- Local Timeline
- \#Introduction

Tags are one of the best built in methods of discovery that Mastodon offers. Feel free to liberally use tags in your future toots.

## \#Introduction and \#Introductions

A tradition on Mastodon is that whenever someone joins they create what we call a \#Introduction post. This is helpful to people new on the platform as others can decide whether to follow back based on a more complete profile, and it helps people like me find like-minded folks. For example, here's mine:

{{< displayToot fosstodon-org-108222429500713598 >}}

Here's what empty profiles look like to us:

{{< displayToot fosstodon-org-108269796505838110 >}}

## FediFollows

FediFollows@mastodon.online is an account that regularly recommends new accounts to follow. In fact, they even have these accounts [organized by topic](https://mastodon.online/@FediFollows/108276705471084305). Here's an example of a recent toot as of the time of writing:

{{< displayToot mastodon-online-108307925251519968 >}}

I recommend you follow FediFollows and checkout any profiles that interest you!

## Trunks

While FediFollows provides recommendations of accounts to follow (both organizations and fellow humans), trunks provide a list of people to follow by topic.

https://communitywiki.org/trunk

The list is maintained by a few kind volunteers stated on the webpage. People can sign up to be on multiple trunks by messaging the admins.

## Fediverse.info

The last resource that I'll share is https://fediverse.info. This is like the trunks above where it's a site that maintains lists of accounts organized by topic. However, instead of being manually vetted by a few admins, anyone can add their profile to this website. The full instructions are on the website but it's based on tags in one's bio.

## Conclusion

The lack of recommendation engine has driven the Mastodon community to create new and novel ways of discovering new people. It wouldn't surprise me if within the year a whole new set of tools are made available to us. Though I have to say, the default of not showing unfollowed accounts in our feeds is really nice. It means that our Mastodon experience is truly unique to us, and that we can curate them to our liking.
