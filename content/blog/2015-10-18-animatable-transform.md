---
id: 337
title: 'Animatable: Transform'
date: 2015-10-18T16:32:37+00:00
author: Brandon Rozek
aliases:
    - /2015/10/animatable-transform/
permalink: /2015/10/animatable-transform/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"1eb4fcf6a5df";s:21:"follower_notification";s:3:"yes";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:66:"https://medium.com/@brandonrozek/animatable-transform-1eb4fcf6a5df";}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"1eb4fcf6a5df";s:21:"follower_notification";s:3:"yes";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:66:"https://medium.com/@brandonrozek/animatable-transform-1eb4fcf6a5df";}'
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
tags: ["Web", "CSS"]
---
This is the last post of the animatable series. The grand finale. Here, we will talk about the transform property. It’s only one property but it comes with a lot of goodies in the form of transform-functions.

<!--more-->

This is not a comprehensize list. If you want one of those, please check out MDN. They have a great [resource](https://developer.mozilla.org/en-US/docs/Web/CSS/transform-function). This is the last post of the animatable series, I recommend you check out the other parts too.

  * Part 1 — [Animatable: Border](https://brandonrozek.com/2015/05/animatable-border/)
  * Part 2 — [Animatable: Box Model](https://brandonrozek.com/2015/09/animatable-box-model/)
  * Part 3 — [Animatable: Text](https://brandonrozek.com/2015/10/animatable-text/)
  * Part 4 — [Animatable: Location](https://brandonrozek.com/2015/10/animatable-location/)
  * Part 5 — [Animatable: Visual](https://brandonrozek.com/2015/10/animatable-visual/)

Animatable: Transform goes with a [CodePen demo](http://codepen.io/brandonrozek/full/ojoMyE){.broken_link} I made. Please check it out, as I will be referencing it later on in the post.

### rotate()

The rotate() function moves the element around a fixed point as defined by the [transform-origin](https://developer.mozilla.org/en-US/docs/Web/CSS/transform-origin) property. In the Codepen demo (#1), the star continously rotates 360 degrees.

```css
@keyframes rotate {
  to { transform: rotate(360deg);}
}

.rotate {
  width: 6rem;
  height: 6rem;
  background-image: url("https://upload.wikimedia.org/wikipedia/commons/thumb/5/51/Star_full.svg/2000px-Star_full.svg.png");
  background-size: cover;
  transform: none;
  animation: rotate 1s ease 0s infinite;
}
```

### scale()

Scale(sx, sy) modifies the size of the element by taking 2 arguments: sx and sy. Where sx is the multiplier that scales the element in the x-direction while sy is the multiplier that scales the element in the y-direction. In the CodePen demo (#2), the little ninja man scales to half his size and back to normal again.

```css
@keyframes scale {
  to { transform: scale(.5); }
}

.scale {
  width: 6rem;
  height: 6rem;
  background-image: url("https://upload.wikimedia.org/wikipedia/commons/7/71/Monocromaticman.JPG");
  background-size: contain;
  background-repeat: no-repeat;
  transform: none;
  animation: scale 1s ease 0s infinite alternate;
}
```

### skew()

Skew distorts the element by moving each point to a certain angle determined by it’s distance from the origin. In the CodePen demo (#3), the square skews -20 degrees, making it appear as a parallelogram.

```css
@keyframes skew {
  to { transform: skew(-20deg); }
}

.skew {
  height: 6rem;
  width: 6rem;
  background-color: lightblue;
  transform: none;
  animation: skew .75s ease 0s infinite alternate;
}
```

### translate()

Transform(tx, ty) moves the element as specified by it’s two parameters tx and ty. Tx tells the browser how many units to move it in the x direction while ty tells the browser how many units to move the element in the y direction. In the CodePen demo (#4), the car moves forward 10rem and back again.

```css
@keyframes translate {
  to { transform: translate(10rem);}
}

.translate {
  height: 6rem;
  width: 6rem;
  background-image: url("http://res.freestockphotos.biz/pictures/15/15685-illustration-of-a-red-cartoon-car-pv.png");
  background-size: contain;
  background-repeat: no-repeat;
  transform: none;
  animation: translate 1s ease 0s infinite alternate;
}
```

### Conclusion

It is now the end of the Animatable series. I am sad to see this first completed series of mine go. It’s okay though, I’m bound to think of another series to write for you guys in no time. My goal in Animatable, is to show you (and me) what is possible using CSS animations. With this small reference completed, we have a good overview of the different tools available. Now with our new toolbelt, go out and craft meaningful experinces!
