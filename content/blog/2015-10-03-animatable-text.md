---
id: 148
title: 'Animatable: Text'
date: 2015-10-03T08:44:51+00:00
author: Brandon Rozek
aliases:
    - /2015/10/animatable-text/
permalink: /2015/10/animatable-text/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"8ef239deb1ea";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:61:"https://medium.com/@brandonrozek/animatable-text-8ef239deb1ea";}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"8ef239deb1ea";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:61:"https://medium.com/@brandonrozek/animatable-text-8ef239deb1ea";}'
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
kind:
  - article
tags: ["Web", "CSS"]
---
This post is part 3 of my series on animation. In this post, I'll show you different animations you can add onto text. If you haven't already, you should check out [part 1](https://brandonrozek.com/2015/09/animatable-box-model/) and [part 2](https://brandonrozek.com/2015/05/animatable-border/) of this series. Animations on text can be used to bring attention, to add importance, or to convey a point. As with all animations, however, keep your user in mind and your text readable.

<!--more-->

This post follows along with a [Codepen demo](http://codepen.io/brandonrozek/full/dYGwbE/){.broken_link} I made.

### line-height

  * Accepts certain keywords, or any positive number or length
  * Initial value: normal

Line-height is the space between each line in a text block. It is commonly recommended that you use a unitless line-height because then it takes the font-size into consideration. When you use an unitless value, the browser determines the line-height by taking the unitless value and multiplying it by the element's font-size. In the Codepen demo (#1), you can see the line-height decreasing while the opacity increases.

```css
@keyframes line-height {
  to {
    opacity: 1;
    line-height: 1.2;
  }
}

.line-height {
  opacity: 0;
  line-height: 2.5;
  animation: line-height .75s ease .2s infinite;
}
```


### font-weight

  * Accepts certain keywords or 100, 200, 300, 400, 500, 600, 700, 800, 900 (the higher the number, the darker the font-weight)
  * Initial value: normal

Font-weight specifies the boldness of the text. If the typeface doesn't come with multiple weights, then the animation would only happen between the weights that it does have. In the demo (#2), the text will go from normal weight to bold.

```css
@keyframes font-weight {
  to { font-weight: 900;}
}

.font-weight {
  font-weight: 100;
  animation: font-weight 2s linear .2s infinite alternate;
}
```

### font-size

  * Accepts any length
  * Initial value: medium

It is important to note that changing the font-size could change the value of other text properties that are dependent upon it. (Like unitless line-heights) In the demo (#3), you can see the text's font-size shrinking.

```css
@keyframes font-size {
  to { font-size: .1rem;}
}

.font-size {
  font-size: 2rem;
  animation: font-size 2s ease-out  .1s infinite;
}
```

### text-shadow

  * Accepts a color and 3 lengths
  * Color | Offset-X | Offset-Y | Blur-radius
  * Initial value: none

Text-shadow applies a shadow to both the text and its text-decoration. Multiple shadows can be added, and they are applied from front to back. In the animation (#4), you can see the text's shadow move.

```css
@keyframes text-shadow {
  to { text-shadow: 25px 10px 5px rgba(0, 0, 0, .9);}
}

.text-shadow {
    font-size: 1.5rem;
    text-shadow: -10px 5px 3.5px rgba(0, 0, 0, .3);
    animation: text-shadow 1s ease 0s infinite;
}
```

### text-decoration-color

  * Accepts a color value
  * Initial value: currentColor

This sets the color for [text-decoration-line](https://developer.mozilla.org/en-US/docs/Web/CSS/text-decoration-line) (underlines, overlines, or strike-throughs) In the demo (#5), the strike-through changes from red to black.

```css
@keyframes text-decoration-color {
  to { text-decoration-color: black;}
}

.text-decoration-color {
  text-decoration-color: red;
  text-decoration-line: line-through;
  animation: text-decoration-color 2s linear 0s infinite alternate;
}
```


### word-spacing

  * Accepts keywords or positive/negative length
  * Initial value: normal

Word-spacing defines the space between tags and words. Negative values bring the words closer to each other. In the demo (#6), you can see the word-spacing increase with &#8216;good bye!&#8217; where the word &#8216;bye!&#8217; is moving away.

```css
@keyframes word-spacing {
  to { word-spacing: 5rem;}
}

.word-spacing {
  word-spacing: normal;
  animation: word-spacing 1s ease-in 0s infinite;
}
```


### letter-spacing

  * Accepts keywords or positive/negative length
  * Initial value: normal

Letter-spacing specifies the spacing between text characters. Negative values bring the letters closer together. In the demo (#7), each letter gets separated from one another.

```css
@keyframes letter-spacing {
  to { letter-spacing: 2rem;}
}

.letter-spacing {
  letter-spacing: 0;
  animation: letter-spacing .75s ease 0s infinite alternate;
}
```


### Conclusion

These animations show the different things you can do with text. Perhaps you'll add a small animation to a heading to bring depth and attention, or you'll add some to the text of a button to scream &#8220;call to action&#8221;. Whatever you decide, I hope this post helped. I'll see you again next time with another animatable post! 🙂

#### The links

- [https://docs.webplatform.org/wiki/css/properties/line-height](https://developer.mozilla.org/en-US/docs/Web/CSS/line-height)
- https://developer.mozilla.org/en-US/docs/Web/CSS/line-height
- https://docs.webplatform.org/wiki/css/properties/font-weight
- https://developer.mozilla.org/en-US/docs/Web/CSS/font-weight
- https://docs.webplatform.org/wiki/css/properties/font-size
- https://developer.mozilla.org/en-US/docs/Web/CSS/font-size
- https://docs.webplatform.org/wiki/css/properties/text-shadow
- https://developer.mozilla.org/en-US/docs/Web/CSS/text-shadow
- https://docs.webplatform.org/wiki/css/properties/text-decoration-color
- https://developer.mozilla.org/en-US/docs/Web/CSS/text-decoration-color
- https://docs.webplatform.org/wiki/css/properties/word-spacing
- https://developer.mozilla.org/en-US/docs/Web/CSS/word-spacing
- https://docs.webplatform.org/wiki/css/properties/letter-spacing
- https://developer.mozilla.org/en-US/docs/Web/CSS/letter-spacing
