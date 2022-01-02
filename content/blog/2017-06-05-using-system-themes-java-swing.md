---
id: 2192
title: Using System Themes In Java Swing
date: 2017-06-05T20:36:22+00:00
author: Brandon Rozek
layout: post
guid: https://brandonrozek.com/?p=2192
aliases:
    - /2017/06/using-system-themes-java-swing/
permalink: /2017/06/using-system-themes-java-swing/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
mf2_syndicate-to:
  - 'a:1:{i:0;s:4:"none";}'
mf2_cite:
  - 'a:4:{s:9:"published";s:25:"0000-01-01T00:00:00+00:00";s:7:"updated";s:25:"0000-01-01T00:00:00+00:00";s:8:"category";a:1:{i:0;s:0:"";}s:6:"author";a:0:{}}'
tumblr_post_id:
  - "161478693279"
mf2_syndication:
  - 'a:1:{i:0;s:60:"https://twitter.com/B_RozekJournal/status/871828083459936257";}'
kind:
  - article
tags: ["Java"]
---
The default theme for Java Swing components is a cross-platform theme called &#8220;Metal&#8221;. I use the Adapta theme for GTK on Linux and this theme does not match at all what my other GUI applications look like. So here, I will describe a simple way to utlize already existent system themes in Java Swing applications.

<!--more-->

### Solution

In the init method of your java application, place the following code.

<pre class='language-java'><code class='language-java'>
try {
    UIManager.setLookAndFeel(UIManager
                               .getSystemLookAndFeelClassName());
} catch(Exception e) {}
</code></pre>

Here the application will attempt to look up the system theme and set that as the default styles for the Swing components. If the lookup fails, then it will default back to the metal theme.

For more information, check out this page from [Oracle](http://docs.oracle.com/javase/tutorial/uiswing/lookandfeel/plaf.html).

### Discussion

If it is so easy to set up applications that look native to each desktop environment, why not have that by default? With the cross platform metal theme, you can ensure that the style of your application is the same across all the operating systems. In this fashion, you don&#8217;t need to worry about spacing between components and have full control of the &#8220;look and feel&#8221; of your application. 

Since I am used to development for the web, I don&#8217;t have strong motivation to have an application look the same on all platforms. I prefer the application to match the system theme and look like it was built for the platform that I am on. One loses partial control on the presentation of your application across different desktop environmnets, but with a strong layout, it is possible to make it look organized and integrated.