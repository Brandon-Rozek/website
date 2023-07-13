---
title: "Proactive Defederation, is it worth it?"
date: 2023-07-10T07:56:01-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

Meta recently launched Threads in an effort to siphon dissatisfied Twitter users. In this process, they are rumored to pursue ActivityPub support. This would allow users on Mastodon and other Fediverse platforms to communicate with people on Threads.

The rumor has been circulating for a few months now, even when Threads was referred to its codename *Project 92*. As such, many people have already voiced their opinion of this move. A group of moderators even banded together to make a [website declaring their opposition of Meta joining the Fediverse](https://fedipact.online/).

The general argument is that Facebook is *bad* and [has a bad track record](https://seirdy.one/posts/2023/06/20/defederating-p92/#incompatible-values-and-complicity). Thus, many people from the Mastodon community want to disassociate from Meta. The tool for disassociation on the Fediverse is called *de-federation*.

The idea behind the Fediverse is that servers can *federate* with each other. This means that servers can share data (whether its statuses or posts) with other servers as they talk a common language. Admins of each of these servers can select which platforms they want to *block*. Refusing to display content from blocked servers is called de-federation.

This technique is commonly used to block content from servers that often promote illegal or offensive content. Though it can also be used in cases where servers do not align with the ethics of a community. Since Facebook "does not match the moral compass" of several Mastodon communities, they seek to de-federate proactively. Before any questionable content appears.

The hope of these admins, is that if enough servers de-federate, it effectively nulls the benefits of adding ActivityPub support. Blocking the millions of users that signed up for Threads from interacting with other Mastodon users.

Of course, there will be some server admins that prioritize free speech and alternative values, but we'll get into that later...

Instead of going further into the ethics of the situation. I'm curious on the potential ramifications of Threads both sucessfully and unsucessfully federating with the majority of the Fediverse.

## Successful Federation

Lets say somehow Threads manages to federate with enough servers, such that the majority of current Mastodon users can interact with Threads users.

In this world, Threads will be by far the largest user instance. This would not be too unexpected, since they have the engineers on staff to build infrastructure that can support millions of people. As a consequence, the majority of content would then be generated via Threads.

This content will likely not follow the cultural norms of the existing Mastodon community. The majority of these cultural norms are built with an accessibility first mindset. Examples of this include: adding captions to photos, title-casing hashtags, adding content warnings to inappropriate or sensitive topics.

In a world where Meta is the largest Fediverse player, they will likely try to push the ActivityPub standards to whatever their priority of the time is. There's a few ways this can play out, they can try to be the majority representation of the board updating the ActivityPub standard. They could also just implement features themselves and bully others to adopt and support the extensions to the standard they craft.

What features do I imagine Meta will want to add? I would imagine any that pertain to advertising and monetization, but we can leave that to your imagination.

## Failed Federation

In this world, enough large instances de-federate from Threads, that most current users of Mastodon wouldn't see content from them.

The ideal in this case is that some sort of status quo is maintained and users of these differing communities do not need to interact with each other. 

Though I'm not sure if that's the case. There might be some internal resistance from Mastodon users that want to use the Fediverse to keep in touch with their friends and family. Sadly the majority of non-techie friends and family will likely be using Threads or another platform from a major player. This added pressure can either cause the de-federated servers to federate again. Alternatively, it can cause some of these users to migrate over to free speech-instances or create another account on these or on Threads itself.

Unfortunately for many free-speech instances, they often harbor offensive speech. The question then is: does Threads federate with these servers and then have to take many active measures to make sure the most extreme content doesn't surface to its users?

Or does it just block the free-speech instances entirely? If Threads de-federates from the free speech instances, then there wouldn't be enough other instances to federate with making this a failed ActivityPub  attempt.

There could be an attempt to fork the ActivityPub standard, but without some buy-in from the existing community, this is likely to fail.

## Conclusion

Historically, this reminds me of when Google Talk/Hangouts supported XMPP. At the time I used Pidgin with the OTR plugin to communicate with friends and family. Sadly they henceforth abandoned XMPP support and I don't use much of that or Hangouts anymore.

Will we see a similar approach from Meta to extend, embrace, and extinguish the ActivityPub protocol?

