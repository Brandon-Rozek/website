---
title: "Custom System Fonts"
date: 2019-05-27T12:15:25-04:00
draft: false
aliases:
    - /blog/adding-fonts
---

**Warning: This blog post partially applies to Ubuntu-based operating systems**

I wanted to add a font to an image on GIMP. Now I wanted to make it so that the font is available system-wide in case I ever needed it again.

Following this [blog post from It's FOSS](https://itsfoss.com/install-fonts-ubuntu/) I decided to make a `.fonts` folder in my home directory. After that you can download various font's from [Font Squirrel](https://www.fontsquirrel.com/), [dafont](https://www.dafont.com), [Google Fonts](https://fonts.google.com/), and others and drop the `.otf` or `.ttf` files into the `.fonts` folder.

Then to finally achieve my goal, I made sure I added `/home/user/.fonts` folder to my fonts as outlined on the [GIMP documentation](https://docs.gimp.org/2.10/en/gimp-using-fonts.html)