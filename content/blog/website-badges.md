---
title: "Adding badges to my website"
date: 2023-11-26T22:57:08-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

I've been coming across more [neocities](https://neocities.org/) websites recently. It's really cool how many people there hand craft their HTML and CSS to really make a website theirs. One idea I'm stealing for my website is adding web badges.

![Example Badge](/badges/fedora.gif)

These web badges are often small images that shows a product or message. Historically, it dates back to when Netscape in 1996 made the [Netscape Now!](https://sillydog.org/netscape/now.html) badge. 

Since then, the Geocities picked it up and standardized many of the web badges to have a pixel size of 88x31. These badges are sometimes animated as GIFs, though they usually don't hold dynamic information.

In recent times, we've seen badges hold dynamic information such as [code coverage on GitHub](https://github.com/badges/shields). Also, Wikipedia has Userboxes that people can add to their User Pages to show dynamic information about themselves. [Ruben's User Page](https://en.wikipedia.org/wiki/User:RubenSchade/Userboxes) showcases many of these.

Though to get started with my own website, I decided to look primarily at the traditional 88x31 style web badges. Looking around the web, there are some webpages that have large listings of web badges:

https://web.badges.world/

https://cyber.dabamos.de/

https://capstasher.neocities.org/

From there, we can (1) pick the ones we like (2) download them, and (3) upload them to our webserver. We can then create the `img` tag in our footer to showcase them.

```html
<img width="88px" height="31px" src="/badges/fedora.gif" />
```

