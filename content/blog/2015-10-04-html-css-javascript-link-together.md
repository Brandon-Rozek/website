---
id: 210
title: HTML, CSS, Javascript, and how they all link together
date: 2015-10-04T17:50:50+00:00
author: Brandon Rozek
aliases:
    - /2015/10/html-css-javascript-link-together/
permalink: /2015/10/html-css-javascript-link-together/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"9579f30ae529";s:21:"follower_notification";s:3:"yes";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:96:"https://medium.com/@brandonrozek/html-css-javascript-and-how-they-all-link-together-9579f30ae529";}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"9579f30ae529";s:21:"follower_notification";s:3:"yes";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:96:"https://medium.com/@brandonrozek/html-css-javascript-and-how-they-all-link-together-9579f30ae529";}'
dsq_thread_id:
  - "4194222476"
  - "4194222476"
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
tags: ["Web"]
---
I've been teaching a small class on web development recently, and after my first lecture, I've gained a newfound respect for teachers. Teaching didn't come as naturally to me as I would have imagined. I tried going in prepared: with a few outlines and a few code demos. Instead of letting my preparation go to waste, I decided to share them here with you on my site. It's a nice break from the Animatable posts, so I hope you enjoy!

<!--more-->

I suggest a couple short readings to check out before the lecture:

  * [What is CSS](http://www.sitepoint.com/web-foundations/css/) by Adam Roberts
  * [Box Model](http://www.w3.org/TR/CSS2/box.html) by the W3C

Take a quick look if you wish. These are mostly to give an idea of what is going to happen over the next few lectures. What is HTML, CSS, and Javascript? We'll look into the different parts that form a webpage and how they all interact with each other.

## HTML

HTML is where the content of your site lives. It's also the file the server returns to no matter what, the bare-bones of a webpage. This file may contain text, pictures, and/or other media.

## CSS

This is where you style your content. Whether it's through colors, layout, or typography, there are plenty of different ways for you to visually manipulate your content.

## Javascript

Javascript is where you add functionality of your site. Validating user input or having dynamic content are one of the many things you can do with Javascipt.

## How do they all link together?

HTML, CSS, and Javascript each do what they do the best. So how can you have them all play nicely on the same ball field?

### In HTML

Link the CSS file

```html
<link rel='stylesheet' href='style.css'>
```

Link the Javascript file

```html
<script src='script.js'></script>
```

Give the `<p>` tag a class of hello and id of world to use in CSS and Javascript

```html
<p class='hello' id='world'></p>
```

### In CSS

Refer to any element with `class='hello'` and change it's text color to red.

```css
.hello { color: red; }
```

Any element with an `id='world'` will have it's font-size changed to 2rem

```css
#world { font-size: 2rem; }
```


You don't have to only use the class and id attributes in html, you can refer to any attribute. This code snippet grabs any canvas element with `data='sales'` and changes it's border to be 5px thick, dashed, and the color blue.

```css
canvas[data=sales] { border: 5px dashed blue; }
```

### In Javascript

Javascript has many properties and methods you can use to reference different HTML elements To grab (an) element(s)

```js
document.getElementById();
document.getElementsByClassName(); //Returns an array of element(s)
document.querySelector(); //Returns the first matching selector
document.querySelectorAll(); //Returns an array of element(s)
```

To add a class to an element

```js
element.className += “ random-class” //Note the space

```

To check whether a certain condition is true in the browser

```js
window.matchMedia('aspect-ratio: 12/8'); //Returns true if the aspect ratio is 12/8
window.innerHeight; //Is the height of the window
window.innerWidth; //Is the width of the window
```

_And a lot more_

## What should handle what?

HTML, CSS, and Javascript should all handle what each of them does best. HTML should handle the content, CSS should handle the styles/presentation, and Javascript should handle the behavior of the webpage. Why, you ask? One reason is that it demonstrates a &#8220;separation of concerns&#8221;. It would be a mess if you're writing an article in the HTML and you put style attributes all over the place. That would make the markup confusing and hard to read/edit.

## Can't I just put everything in a Javascript file?

Yes you can, but then you lose some of the great features of HTML and CSS. HTML and CSS ignore everything that it doesn't understand. When Javascript encounters something it doesn't understand, it stops running the code completely, regardless of what comes after. Please note that I am only speaking about what gets served to the user. When it comes to what's actually on your server, then store your content however you wish.

## Conclusion

To me personally, my first lecture was a mess. Some of my examples didn't work properly in the first type-through and I was everywhere. Though, to be sharing the little knowledge I do have, comes with its own joy. It must not have gone as terrible as I imagined it in my head because they seemed enthusiastic for the next lecture. So I'm excited to share this outline with you, and hopefully I'll have many more to come. Until next time. 🙂