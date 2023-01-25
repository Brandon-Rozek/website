---
id: 2174
title: Viewing Java Applets
date: 2017-05-24T15:59:45+00:00
author: Brandon Rozek
aliases:
    - /2017/05/viewing-java-applets/
permalink: /2017/05/viewing-java-applets/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
mf2_syndicate-to:
  - 'a:1:{i:0;s:22:"bridgy-publish_twitter";}'
mf2_cite:
  - 'a:4:{s:9:"published";s:25:"0000-01-01T00:00:00+00:00";s:7:"updated";s:25:"0000-01-01T00:00:00+00:00";s:8:"category";a:1:{i:0;s:0:"";}s:6:"author";a:0:{}}'
mf2_syndication:
  - 'a:1:{i:0;s:60:"https://twitter.com/B_RozekJournal/status/867409810932760576";}'
tags: ["Java"]
---
When you use an IDE there are many things you can take for granted. A section of an intro level computer science course at my university uses [JGrasp](http://www.jgrasp.org/) to build Java Applets.

Following around using a normal text editor, I found that I couldn&#8217;t just compile and run the code like I have with my java programs in the past. To be able to help around and assist in the course, I need to be able to build and run these applications. The rest of this article describes the process I underwent to be able to use my existing setup to write and build java applets. Of course you can always install JGrasp and have that all built in, but it&#8217;s always nice to not have to change your workflow.

<!--more-->

When I tried following along, I would receive the following error

    Main method not found in class HelloWorld, please define main method as...

Which makes sense since I have never defined a main method inside my source code. So how do I go about doing this?

## Setup

Java Applets are meant to run on web pages, because of this one needs an html file to host the applet. The following code gives you the bare minimum for setting up the html file. I called it `HelloWorld.html`.

<pre class='language-html'><code class='language-html'>
&lt;html&gt;
    &lt;head&gt;&lt;title&gt;Applet Container&lt;title&gt;
    &lt;body&gt;
        &lt;applet code='HelloWorld.class' width=400 height=400&gt;&lt;/applet&gt;
    &lt;/body&gt;
&lt;/html&gt;
</code></pre>

## Hello World Program

To get it up and running, I will show a &#8220;Hello World&#8221; like application for applets.

<pre class='language-java'><code class='language-java'>
import javax.swing.JApplet;
import java.awt.Graphics;

public class HelloWorld extends JApplet {
    public void paint(Graphics g) {
        g.drawString("Hello World", 30, 30);
    }
} 
</code></pre>

## Running the Applet

Now we need to compile the code

<pre class='langauge-bash'><code class='language-bash'>javac HelloWorld.java</code></pre>

Then run the appletviewer

<pre class='language-bash'><code class='language-bash'>appletviewer HelloWorld.html</code></pre>

## Conclusion

This tutorial concludes the setup of running a simple Java applet. From here you can look at the different methods in the [Graphics library](https://docs.oracle.com/javase/7/docs/api/java/awt/Graphics.html) and play around 😀