---
title: "Mapping the states I visited"
date: 2024-02-01T18:30:00-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

[Henrique's Impossible List](https://hacdias.com/impossible-list/) shows a list of countries that they've visited so far and their goals for the future. I personally have not travelled to many countries, but I have visited a several US states!

Instead of presenting the states in a list, I thought it would be very cool to visually show it on a map. Ideally the map would be encoded in a SVG so that:

- The image will scale regardless of the device size
- I can manually edit the source to show the visited regions

Now imagine my surprise after searching on [Kagi](https://kagi.com/) to come across a SVG in the public domain on [Wikipedia](https://commons.wikimedia.org/wiki/File:Blank_US_Map_(states_only).svg). Even better, the following is shown near the top of the file

```css
/* Individual states can be colored as follows: */
.ks,.mt,.pa {fill:#0000FF}
.ca,.de {fill:#FF0000}
/* In this example, Kansas, Montana and Pennsylvania are colored blue,
and California and Delaware are colored red.
Place this code in the empty space below. */
```

Such an elegant way of coloring in the states! Now it's up to me to come up with some categories. As of the time of writing, I decided on:

- Green: Places I've lived
- Blue: Places I've visited
- Darker Gray: Places I've driven through

Here's how I colored by map:

![Map of US States colored by whether I've visited](/files/images/usa_visited.svg)

For the last couple weeks, I've been brainstorming new pages for my website and came up with https://brandonrozek.com/visited.

At the time of writing, it only has the colored in states and a list of cities I've been to. Though I'm welcome to any suggestions you might have. Feel free to [get in touch!](/contact)
