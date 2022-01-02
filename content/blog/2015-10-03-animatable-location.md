---
id: 190
title: 'Animatable: Location'
date: 2015-10-03T09:34:08+00:00
author: Brandon Rozek
layout: post
guid: https://brandonrozek.com/?p=190
aliases:
    - /2015/10/animatable-location/
permalink: /2015/10/animatable-location/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"ad9e6109d5aa";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:65:"https://medium.com/@brandonrozek/animatable-location-ad9e6109d5aa";}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"ad9e6109d5aa";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:65:"https://medium.com/@brandonrozek/animatable-location-ad9e6109d5aa";}'
dsq_thread_id:
  - "4194325357"
  - "4194325357"
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
tumblr_post_id:
  - "135657326384"
  - "135657326384"
kind:
  - article
tags: ["Web", "CSS"]
---
Animating the location of objects is one of the most common types of animation. It&#8217;s interesting to animate this way because you need to keep in mind how each of the element&#8217;s interact with each other to constitute a page.

<!--more-->

This is part 4 of my series on animation. Check out the other parts of this series!

  * Part 1 — [Animatable: Border](https://brandonrozek.com/2015/05/animatable-border/)
  * Part 2 — [Animatable: Box Model](https://brandonrozek.com/2015/09/animatable-box-model/)
  * Part 3 — [Animatable: Text](https://brandonrozek.com/2015/10/animatable-text/)

This post goes along well with this [Codepen demo](http://codepen.io/brandonrozek/full/NGbWzo/){.broken_link}, I&#8217;ll reference it multiple times in this post. Now onto animations!

### background-position

  * Accepts keywords, percentages, or lengths
  * Offset-x | Offset-Y
  * Initial Value: 0% 0%

Background-position sets where the background is relative to it&#8217;s background-origin. In the Codepen demo (#1), you can see the background image scrolling horizontally.

<pre><code class="language-css"> 
@keyframes background-position {

 to { background-position: 100% 0%; }

}

.background-position {
  background-image: url(https://upload.wikimedia.org/wikipedia/commons/d/d3/Tajik_mountains_edit.jpg);

  height: 6rem;

  width: 8rem;

  background-size: 200% 100%;

  background-position: 0% 0%;

  animation: background-position 5s linear .1s infinite alternate;

}
</code></pre>

### position with left, right, top, bottom

  * Accepts length, percentage, or some keywords
  * Initial value: auto

The left, right, top, and bottom properties require the position to be set to something other than static. When you add a value to any of these properties just imagine that value pushing the element on that side. For example: for &#8220;left: 2rem&#8221; imagine that the element is being pushed on the left side by 2rem, making it move to the right 2rem. In the demo (#2), the box is being pushed in a square path.

<pre><code class="language-css">
@keyframes position {

  25% {

    top: 0;
    
    left: 3rem;

  }

  50% {

    top: 3rem;
    
    left: 3rem;

  }

  75% {

    top: 3rem;
    
    left: 0;

  }

}

.position {

  position: relative;

  top: 0;

  left: 0;

  height: 3rem;

  width: 3rem;

  background-color: lightblue;

  animation: position 1.5s ease .1s infinite;

}
</code></pre>

 

### vertical-align

  * Accepts keywords, percentages, or lengths (Negative values allowed)
  * Initial Value: baseline

Vertical-align sets how vertically the inline element or text is compared to the baseline. In the Codepen demo (#3), the question has its vertical align being manipulated which causes the &#8220;Maybe&#8221; to bounce up and down.

<pre><code class="language-css">
@keyframes vertical-align {

  to { vertical-align: 1rem; }

}

.vertical-align {

  font-size: 1.5rem;

  vertical-align: 0;

  animation: vertical-align 1s ease-out .1s infinite alternate;

}
</code></pre>

### z-index

  * Accepts any integer value
  * Initial Value: auto

If elements overlap, z-index determines which element appears on top. If the z-index is the same, then it is controlled by source order. In the demo (#4), The z-index of the biggest box changes, revealing what is under it.

<pre><code class="language-css">
@keyframes z-index {

  to { z-index: 0; }

}

.z-index {

  position: absolute;

  left: 1rem;

  display: inline-block;

}

.z-index:nth-child(1) {

  height: 1rem;

  width: 1rem;

  background-color: lightgreen;

  z-index: 4;

}

.z-index:nth-child(2) {

  height: 2rem;

  width: 2rem;

  background-color: #F4FFA4;

  z-index: 3;

}

.z-index:nth-child(3) {

  height: 3rem;

  width: 3rem;

  background-color: #DEB0ED;

  z-index: 2;

}

.z-index:nth-child(4) {

  height: 4rem;

  width: 4rem;

  background-color: #D8EADF;

  z-index: 5;

  animation: z-index 1s ease .1s infinite alternate;

}
</code></pre>

### Conclusion

By animating the location of an element, it opens up a whole bunch of different opportunities. Using motion, you can signify that the user has indeed pressed the button, instead of what would otherwise leave them there clicking on the button multiple times thinking that nothing has happened. Using motion, you can bring a webpage that would&#8217;ve otherwise been boring to life. Use these animations to work, and I&#8217;ll be back with another animatable post soon!

#### The links

<https://developer.mozilla.org/en-US/docs/Web/CSS/background-position> <https://developer.mozilla.org/en-US/docs/Web/CSS/left> <https://developer.mozilla.org/en-US/docs/Web/CSS/vertical-align> <https://developer.mozilla.org/en-US/docs/Web/CSS/z-index> <https://docs.webplatform.org/wiki/css/properties/background-position>{.broken_link} <https://docs.webplatform.org/wiki/css/properties/left>{.broken_link} <https://docs.webplatform.org/wiki/css/properties/vertical-align>{.broken_link} <https://docs.webplatform.org/wiki/css/properties/z-index>{.broken_link}