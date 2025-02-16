---
id: 85
title: 'Animatable: Border'
date: 2015-05-23T19:59:25+00:00
author: Brandon Rozek
layout: post
guid: http://brandonrozek.com/?p=85
aliases:
    - /2015/05/animatable-border/
permalink: /2015/05/animatable-border/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
dsq_thread_id:
  - "3807156267"
  - "3807156267"
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
tags: ["Web", "CSS"]
---
This is part 1 of an animation series I'm doing. It is inspired by Lea Verou's talk called &#8220;[The Humble Border-Radius.](https://www.youtube.com/watch?v=JSaMl2OKjfQ)&#8221; I looked at her site and she has a good demo of a bunch of different animations [here](http://lea.verou.me/2011/10/animatable-a-css-transitions-gallery/). My goal here is to create a more comprehensive guide to these different animatable properties&#8211;mainly for future reference. Animations play a big part in adding interactivity to the web, so why not explore some possible options?

<!--more-->

This post follows well along with my Codepen [demo](http://codepen.io/brandonrozek/full/waWMWR/){.broken_link}, where I'll state the box number that applies to what I'm talking about. \*\*Initial values must be explicitly stated, implicit initial values are generally ignored in animation\*\* \*\\*\*In English terms, you must have already stated a value for what you are animating before you animate it\*\**

### Border-color {#border-color}

  * Accepts 1 to 4 color values
  * Each value corresponds to each side of the border (starting from the top and going clockwise)
  * Initial Value: currentColor

Border-color animates by splitting the colors to their red, green and blue components and raises/lowers them to its new value. ([Demo](http://codepen.io/brandonrozek/pen/PqzPMe){.broken_link}) ([Spec](http://www.w3.org/TR/css3-transitions/#animtype-color)) Example of animation corresponds to #1 in the pen, but I will rewrite the relevant code here.

```css
@keyframes color {
    to { border-color: purple red green blue; }
}

.border-color {
    border-color: white;
    animation: color .4s ease-in .1s infinite alternate;
}
```

 

### Border-radius {#border-radius}

  * Accepts 1 to 4 values for both horizontal and vertical radii
  * Each value corresponds to a corner starting from the top left and going clockwise
  * Initial Value: 0

```css
.border-radius {
    border-radius: 40% 30% 60% 50% / 20% 40% 60% 80%;
    /** is the same as **/
    border-top-left-radius: 40% 20%;
    border-top-right-radius: 30% 40%;
    border-bottom-right-radius: 60% 60%;
    border-bottom-left-radius: 50% 80%;
    /** where the first value is the horizontal
    radius and the second value the vertical radius **/
}
```

For animation, this corresponds to #2 in the pen I made at the top. I&#8217;ll repeat the relevant code here.

```css
@keyframes radius {
    to { border-radius: 20%; }
}

.border-radius {
    border-radius: 0;
    animation: radius .5s ease-in .1s infinite alternate;
}
```

 

### Border-width {#border-width}

  * Accepts 1 to 4 values
  * Each value corresponds to a side of the border (starting from the top and going clockwise)
  * Initial Value: medium

For animation, this corresponds to #3 in the pen I made at the top. I&#8217;ll repeat the relevant code here.

```css
@keyframes width {
    to { border-width: .15rem .25rem .15rem .25rem; }
}

.border-width {
    border-width: .7rem;
    animation: width .5s ease-in .1s infinite alternate;
}
```

 

### Conclusion

Animations are quite enjoyable. The last box in my Codepen demo tries combining all three of those animations. (Super Wacky!)  You don't need to use keyframe animations to achieve this, you can also use the transition property. I used keyframes so you can better visualize what's going on. There are plenty of other animatable properties to go through, so I'll get started on those. In the meantime, if you want to look at some of the sites I used for research I'll include the links below. 
- <https://developer.mozilla.org/en-US/docs/Web/CSS/animation> 
- <http://www.w3.org/TR/css3-transitions/#animatable-css> 
- <https://developer.mozilla.org/en-US/docs/Web/CSS/border-color> 
- <https://developer.mozilla.org/en-US/docs/Web/CSS/border-radius> 
- <https://developer.mozilla.org/en-US/docs/Web/CSS/border-width> 
- <https://docs.webplatform.org/wiki/css/properties/border-color>{.broken_link} 
- <https://docs.webplatform.org/wiki/css/properties/border-radius>{.broken_link} 
- <https://docs.webplatform.org/wiki/css/properties/border-width>{.broken_link}
