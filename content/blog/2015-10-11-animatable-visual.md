---
id: 297
title: 'Animatable: Visual'
date: 2015-10-11T16:52:36+00:00
author: Brandon Rozek
layout: post
guid: https://brandonrozek.com/?p=297
aliases:
    - /2015/10/animatable-visual/
permalink: /2015/10/animatable-visual/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"c1119f67e27a";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:63:"https://medium.com/@brandonrozek/animatable-visual-c1119f67e27a";}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"c1119f67e27a";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:63:"https://medium.com/@brandonrozek/animatable-visual-c1119f67e27a";}'
tumblr_post_id:
  - "135657496179"
  - "135657496179"
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
kind:
  - article
tags: ["Web", "CSS"]
---
Hello everyone! This is part 5 of my series on animation. Today’s post will be short, since we’re only going to talk about color and opacity.

<!--more-->

I’ll give a shout-out to <http://csstriggers.com>, if you are interested in [CSS Animation performance](https://blogs.adobe.com/webplatform/2014/03/18/css-animations-and-transitions-performance/), then check them out to see what triggers a repaint and/or reflow. Take a look at the other posts in this series!

  * Part 1 — [Animatable: Border](https://brandonrozek.com/2015/05/animatable-border/)
  * Part 2 — [Animatable: Box Model](https://brandonrozek.com/2015/09/animatable-box-model/)
  * Part 3 — [Animatable: Text](https://brandonrozek.com/2015/10/animatable-text/)
  * Part 4 — [Animatable: Location](https://brandonrozek.com/2015/10/animatable-location/)

This post goes with a [Codepen demo](http://codepen.io/brandonrozek/full/rOzeyO/){.broken_link} I made, I’ll reference it later in this post.

### <a href="#color" name="color"></a>color {#color}

  * Accepts any [color](https://developer.mozilla.org/en-US/docs/Web/CSS/color_value) value
  * Typically inherits it&#8217;s color from the parent element

The color property sets the color of an element’s text content and its decoration. During the animation, the browser sees the colors in their red, green, and blue (rgb) components, then increments/decrements those values until it reaches the color it’s animating to. For example, in the Codepen demo (#1), the color of the text is changing from <code class="language-css">red</code> or <code class="language-css">rgb(255, 0, 0)</code> to <code class="language-css">green</code> or <code class="language-css">rgb(0, 255, 0)</code>. Meaning the red component is going from 255 to 0 and the green component is going from 0 to 255 during the animation.

<pre><code class="language-css">@keyframes color {

  to { color: green; }

}

.color {

  font-size: 2rem;

  color: red;

  text-decoration: underline;

  animation: color 1.5s ease-in 0s infinite alternate;

}
</code></pre>

### <a href="#opacity" name="opacity"></a>opacity {#opacity}

  * Accepts any number from [0, 1]
  * Initial Value: 1

Opacity sets the transparency of an element and it’s decendants. Unlike <code class="language-css">display: none;</code>, when the element is <code class="language-css">opacity: 0;</code> the element still holds it’s space on the page. In the Codepen demo (#2), you can see the element and it’s children fading out.

<pre><code class="language-css">@keyframes opacity {

  to { opacity: 0; }

}

.opacity {

  height: 5rem;

  width: 5rem;

  background-color: #cd86e4;

  opacity: 1;

  animation: opacity 2s linear 0s infinite alternate;

}

.opacity div {

  margin-left: auto;

  margin-right: auto;

  height: 3rem;

  width: 3rem;

  background-color: lightblue;

}

.opacity div div {

  margin-left: auto;

  margin-right: auto;

  height: 1rem;

  width: 1rem;

  background-color: #00b300;

}
</code></pre>

### <a href="#conclusion" name="conclusion"></a>Conclusion {#conclusion}

I used to work on a chat application called Babbler. In it, I used opacity to fade in the messages as the user recieved them. With all these different types of animations, you can visually show the user what’s going on in your website/application. Doing this series helps me, (as well as you, I hope) recognize all the different properties and possibilities for animation. This is the second to last part of this series, meaning that the next part is the finale. I’m somewhat sad to see this series ending but excited at the same time. Until next time, have fun animating. 🙂