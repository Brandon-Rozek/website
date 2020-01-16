---
title: "Chirp"
date: 2019-09-27T22:46:52-04:00
draft: false
---

In the land of Ham Radio, you can program your radio with a very popular open source software called `chirp`. For Ubuntu users to install it, it is recommended you use the PPA to keep up to date with radio software...

```bash
sudo apt-add-repository ppa:dansmith/chirp-snapshots
sudo apt update && sudo apt install chirp-daily
```

Once you're in, it is recommended that you download the configuration currently set on your radio and store it somewhere safe. You never know when you'll want the Stock configuration again...

The way the Software works is that you can store a certain amount of channels into your radio. For the Baofeng F8-HP, 128 channels can be stored. The software gives you a table to manage them. The software is nice since you can cut and paste entries around.

When you're importing frequencies from various sources, pay attention to what entry numbers you're importing to. Otherwise you might overwrite another import you've made. I recommend adding the following types of frequencies to your radio...

- Repeaters: Can be added by using RepeaterBook
  - I used proximity search. It takes a zip code and the radius in miles of what you want to import.
- Local frequencies: You need a prenium account from Radio Reference in order to obtain these.
  - Though honestly, a premium account is $15 for half a year. Not bad if you just go in once and download a bunch of frequencies for your area. Depending on where you live, your area might not have frequencies update all the time...
  - Imagine being stuck in traffic and getting to know what's happening around you....
- National Calling Frequencies
- MURS/FRS/GMRS frequencies
- Marine/Railroad frequencies (if you have space)

