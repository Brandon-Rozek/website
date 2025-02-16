---
id: 57
title: Responsive Layout and Animation
date: 2015-04-16T22:19:36+00:00
author: Brandon Rozek
aliases:
    - /2015/04/responsive-layout-and-animation/
permalink: /2015/04/responsive-layout-and-animation/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
dsq_thread_id:
  - "3688354609"
  - "3688354609"
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
tags: ["Web", "CSS"]
---
I saw [Mike Riethmuller&#8217;s](http://madebymike.com.au/) precision typography [pen](http://codepen.io/MadeByMike/pen/YPJJYv){.broken_link}, and was highly impressed. I think the equation used has other purposes as well

<!--more-->

Side Note: I changed the form of the equation to something similar to y = mx + b so that I can more easily recognize how it functions

#### Responsive Layout

There are many occasions where I want an element on the page to move between two points. The navigation in the header of my site (at the time of writing) is a great example of this. So knowing the two points I want it to lie between and having the screen width as the variable, I can plug in&#8230; [<img class="aligncenter size-full wp-image-58" src="https://brandonrozek.com/wp-content/uploads/2015/04/responsivelayoutequation.gif" alt="f(x) = (100 * (b - a)/(d - c))X + (ad - bc) / (d - c)" width="219" height="36" />](https://brandonrozek.com/wp-content/uploads/2015/04/responsivelayoutequation.gif){.broken_link} where a is the start pixel b is the end pixel c is the start media query d is the end media query and X is the screen width out of 100 otherwise known as 1vw \*\*Don't forget to keep track of your units!! Whether it's px/rem/em/etc.\*\* Say I want to push a box towards the right a minimum of 5px, a maximum of 20px and for the push to vary between the widths 400-800px. Then I would write&#8230;

```css
@media (min-width: 400px) and (max-width: 800px) {
    .box {
        position: relative;
        left: calc(3.75vw - 10px) /*After simplifying the equation*/ 
    }
}
```

That would only make it vary between 400-800px. Now we need to include what happens under 400px and over 800px.

```css
@media (max-width: 400px) {
    .box {
        position: relative;
        left: 5px;
    }
}

@media (min-width: 400px) and (max-width: 800px) {
    .box {
        position: relative;
        left: calc(3.75vw - 10px); 
    }
}

@media (min-width: 800px) {
    .box {
        position: relative;
        left: 20px; 
    }
}
```

This is exactly like Mike's pen, but instead he uses the equation to adjust the font-size between an upper and lower bound. You can apply this method to anything that accepts calc() and viewport units. Here is my [pen](http://codepen.io/brandonrozek/pen/JoQVEb){.broken_link} showing some use cases. To make your life easier, I made a quick little tool where you can input the variables and it will provide you with a simpler form of the equation to put into your calc() function [here](http://codepen.io/brandonrozek/pen/KpPwGL){.broken_link}.

#### Animation

This is where the majority of my research went towards. It's not as practical as say positioning an element is but I find it interesting. Like, what if I can manipulate the acceleration of the function? [<img class="aligncenter size-full wp-image-62" src="https://brandonrozek.com/wp-content/uploads/2015/04/accelerationequation.gif" alt="f(x) = ((b - a) / (d^n - c^n))X^n + (ad^n - bc^n) / (d^n - c^n) " width="202" height="36" />](https://brandonrozek.com/wp-content/uploads/2015/04/accelerationequation.gif){.broken_link} Where a is the start unit b is the end unit c is the start time d is the end time n is the acceleration modifier and X is time The interesting part of the function here is the n. If I keep n at 1, then the acceleration is constant. If it's less than one, then it's fast in the beginning and slows down at the end. If it's greater than one, then it's the opposite. I also made a little pen [here](http://codepen.io/brandonrozek/pen/RNzdOV){.broken_link} to demo this for you.

#### Conclusion

Having a function that goes between two points is incredibly handy. Now when it comes to positioning, I don't have to guess which values match the design. If i cant something to be between here and there fluidly, I can do it. What about animation? Chaining them together should have an interesting affect&#8230; P.S For those of you crazy people who like to see the theory behind the math, (like myself) I have my scanned work [here](/blog/2015-04-16-function-two-points-theory/).