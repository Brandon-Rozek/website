---
date: 2022-12-04 21:42:36-05:00
draft: false
math: false
medium_enabled: true
medium_post_id: 5eb712e808ae
tags: []
title: Pretty RSS Feeds
---

Hi, I have a RSS feed. This allows you to subscribe to my words without me even knowing. How does it work? Well you need an RSS link, here's mine:

https://brandonrozek.com/blog/index.xml

Then you need to input this URL into a *newsreader* application ([Feedly](https://feedly.com/), [Feedbin](https://feedbin.com), [NetNewsWire](https://netnewswire.com/), [many others](https://en.wikipedia.org/wiki/Comparison_of_feed_aggregators)) which checks to see if there are any changes in the XML file and presents it in a visually nice way.

In fact, many websites come with a RSS feed. You don't even need to know the exact URL for it to work, if you type in `https://brandonrozek.com` into your newsreader, you'll get options for my various different feeds.

How does that work? Well the website creator needs to include a tag in their website HTML.

```html
<link rel="alternate" 
      type="application/rss+xml" 
      href="https://brandonrozek.com/blog/index.xml" 
      title="Brandon Rozek's Blog" />
```

Most RSS feeds don't come styled. Therefore if you click on the RSS link you'll see a bunch of XML formatted text. That can be confusing for people when they first visit, can we do better?

## About Feeds RSS Style

[Matt Webb](https://interconnected.org/) created https://aboutfeeds.com in order to provide a friendly overview into the world of RSS. As part of that he includes a style called [pretty-feed.xsl](https://github.com/genmon/aboutfeeds/blob/main/tools/pretty-feed-v3.xsl). The file comes with instructions built in, but it's mostly as simple as adding a style tag in the beginning of the XML

```xml
<?xml version="1.0" encoding="UTF-8"?>
<?xml-stylesheet href="/PATH-TO-YOUR-STYLES/pretty-feed-v3.xsl" type="text/xsl"?>
```

I hope more bloggers incorporate the style into their feed. I'm waiting for the day that the largest blogging platform Wordpress includes it by default.