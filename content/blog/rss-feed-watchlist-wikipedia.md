---
title: "How to get a RSS Feed of your Wikipedia Watchlist"
date: 2024-01-07T11:29:01-05:00
draft: false
tags: []
math: false
medium_enabled: false
---

Instead of having to manually log in to Wikipedia to look at your watchlist, you can use your RSS feed!

**Step 1:** Get your token

Go to your [preferences](https://en.wikipedia.org/wiki/Special:Preferences#mw-prefsection-watchlist-token). Log in if not already.

Then click on the *Watchlist* tab. Scroll down to *Tokens*. Click the *Manage Tokens* button.

Hold on to the token for the next step.

**Step 2:** Import the RSS feed to your feed reader.

Direct URL: https://en.wikipedia.org/w/api.php?action=feedwatchlist&allrev&wlowner=USERNAME&wltoken=TOKEN

Replace `USERNAME` and `TOKEN` with their respective information.

**That's it!** Each new item in the RSS feed will look like the following (feed reader dependent):

```
Reinforcement learning
December 31, 2023 at 11:28 PM by OAbot

[[Wikipedia:OABOT|Open access bot]]: arxiv updated in citation with #oabot. (OAbot) 
```

At a glance, you can see:

Line 1: Title of Wikipedia Page Edited

Line 2: Time and Author of Edit (may be username or IP)

Rest: Description of edit.

From here you can check the diffs to make sure that the edit stands.



## Resources

https://m.mediawiki.org/wiki/Help:Watchlist
https://en.m.wikipedia.org/wiki/Wikipedia%3aSyndication
