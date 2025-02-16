---
id: 155
title: 'Animatable: Box Model'
date: 2015-09-14T12:07:52+00:00
author: Brandon Rozek
aliases:
    - /2015/09/animatable-box-model/
permalink: /2015/09/animatable-box-model/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"17293fa1c115";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:66:"https://medium.com/@brandonrozek/animatable-box-model-17293fa1c115";}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"17293fa1c115";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:66:"https://medium.com/@brandonrozek/animatable-box-model-17293fa1c115";}'
dsq_thread_id:
  - "4130257548"
  - "4130257548"
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
tags: ["Web", "CSS"]
---
This post is part 2 of an animation series I am doing; you can read part 1 [here](https://brandonrozek.com/2015/05/animatable-border/). In this post, we'll look at the different parts of the box model (margin, padding, height, and width) and see how they can be animated.

<!--more-->

The W3C has a great starting reference for the [CSS Box Model](http://www.w3.org/TR/CSS2/box.html). It can be wordy at times, but has everything you need to know. I had never heard of _margin collapsing_ until I read that. Luckily there is a great [post](https://css-tricks.com/what-you-should-know-about-collapsing-margins/) on CSS-Tricks written by Geoff Graham explaining what it is. To see it all in action, take a look at this Codepen [demo](http://codepen.io/brandonrozek/full/RWPYgV/){.broken_link}&#8211;  I reference this multiple times in this post. Now, on to the box model.

### Margin

  * Accepts 1 to 4 numerical values (negative numbers are allowed)
  * If you use 4 values, the first value is the top margin and the rest follow in a clockwise fashion
  * Initial value: 0

Margins can be described as the space around an element. In the Codepen demo (#1), it shows 2 boxes. The first box has a margin-right that is increasing, making it seem as though it's pushing the second box away.

```css
@keyframes margin {
  to { margin-right: 7rem; }
}

.margin {
  display: inline-block;
  height: 5rem;
  width: 5rem;
  background-color: lightblue;
  vertical-align: top;
}

.margin:first-of-type {
  margin-right: 0;
  animation: margin 4s ease 0s infinite;
}
```

### Padding

  * Accepts 1 to 4 non-negative values
  * If you use 4 values, the first value is the top margin and the rest follow in a clockwise fashion
  * Initial value: 0

Padding is the space between the content and the border of an element. In the demo (#2),  it shows a box in which its padding is increasing.

```css
@keyframes padding {

to { padding: 2rem; }

}

.padding {
  display: inline-block;
  padding: 0;
  background-color: lightgreen;
  animation: padding 2.5s ease 0s infinite;
}
```


### Height

  * Accepts a non-negative number, this number is overridden however by (min/max)-height
  * Initial value: auto

&#8220;Height&#8221; is the height of an element without its padding, border, or margin. In the demo (#3) you can see the boxes' height shrink, and each box begins its animation at a different time. 

```css
@keyframes height {
  to { height: .01rem; }
}

.height {
  display: inline-block;
  height: 4rem;
  width: 3rem;
  background-color: violet;
  animation: height 1.25s ease 0s infinite;
  vertical-align: top;
}

.height:nth-of-type(n) {
  animation: height 1.25s ease .2s infinite alternate;
}

.height:nth-of-type(2n) {
  animation: height 1.25s ease .4s infinite alternate;
}

.height:nth-of-type(3n) {
  animation: height 1.25s ease .6s infinite alternate;
}
```

### Width

  * Accepts a non-negative number, this number is overridden however by (min/max)-width
  * Initial value: auto

&#8220;Width&#8221; is the width of an element without its  padding, border, or margin. In the demo (#4), it is similar to #3, however, its the width being affected as opposed to the height.

```css
@keyframes width {
  to { width: .01rem; }
}

.width {
  margin-bottom: .2rem;
  height: 3rem;
  width: 6.5rem;
  background-color: bisque;
}

.width:nth-of-type(n) {
  animation: width 1.25s ease .2s infinite alternate;
}

.width:nth-of-type(2n) {
  animation: width 1.25s ease .4s infinite alternate;
}

.width:nth-of-type(3n) {
  animation: width 1.25s ease .6s infinite alternate;
}
```

### Conclusion

And so with this we can add another collection of animations to our toolbelt! If you're wondering why I left border out of this box-model post, its because I have already written a post dedicated to just the [border animation](https://brandonrozek.com/2015/05/animatable-border/). Here are some of the resources I looked at for this post. Hopefully I'll come back with another animatable post soon!


- https://developer.mozilla.org/en-US/docs/Web/CSS/margin
- https://web.archive.org/web/20151112043907/https://docs.webplatform.org/wiki/css/properties/margin
- https://developer.mozilla.org/en-US/docs/Web/CSS/padding
- https://docs.webplatform.org/wiki/css/properties/padding
- https://developer.mozilla.org/en-US/docs/Web/CSS/height
- https://docs.webplatform.org/wiki/css/properties/height
- https://developer.mozilla.org/en-US/docs/Web/CSS/width
- https://web.archive.org/web/20150919163210/https://docs.webplatform.org/wiki/css/properties/width
