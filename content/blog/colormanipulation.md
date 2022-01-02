---
title: "Color Manipulation with Sass"
date: 2019-05-21T23:10:06-04:00
draft: false
tags: ["Web", "CSS"]
---

There are many times that I need to slightly mess with a color. The easiest way I found to do it is to use one of the many color functions in the program `Sass`. [Sass](https://sass-lang.com/) is a CSS preprocessor, meaning that it has it's own syntax and it compiles down to CSS. I remember using this before CSS variables became a thing and that was one of the main driving points of Sass.

Since I don't work in Web Development anymore, I don't actually have Sass installed on my computer but instead go to [SassMeister.com](https://www.sassmeister.com/) to do my color manipulations. ThoughtBot already wrote a really nice [post](https://thoughtbot.com/blog/controlling-color-with-sass-color-functions) describing all the different color functions, but I'll quickly describe what I do to mess with colors.

## Quick Color Manipulation

Now you do need to write special scss syntax in order for this to work, but luckily most of it you can just copy paste and change what you want. For example, to get Sass to make red 10% lighter you would do the following:

```scss
p {
  color: lighten(red, 10%);
}
```

Sass will then output the following:

```css
p {
  color: #ff3333;
}
```

And BAM just like that you got the hex code for a lighter version of red. You can also get all crazy and nest statements into each other which is usually what I do when I play with these colors.

If you rather have the RGBA version of this you can do the following:

```scss
p {
  color: rgba(lighten(red, 10%), 0.5);
}
```

And it will output:

```css
p {
  color: rgba(255, 51, 51, 0.5);
}
```

So in summary, all you need is to replace the section after `color:` and you're all set for manipulating colors! Check out the [ThoughtBot Post above](https://thoughtbot.com/blog/controlling-color-with-sass-color-functions) in order to see all the variety of functions included with Sass such as saturating, hue-shifting, and much more.