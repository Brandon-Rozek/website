---
title: "Dealing with Web Scrapers"
date: 2025-07-02T09:10:23-04:00
draft: false
tags:
  - web scraping
  - CAPTCHA
  - rate limiting
  - robots.txt
  - proof of work
math: false
medium_enabled: false
---

Nowadays it seems like every tech company is eager to scrape the web. Unfortunately, it seems like 
[^1] the majority of traffic that comes to this small site are scrapers. While my static website is able to handle the load, the same cannot be said about everyone.

[^1]: At least I don't think a human using Chrome would try to visit my homepage every minute.

Overall, the techinques I've seen website owners use aim to make scraping more difficult. Though it's a balance. The harder we make it for bots to access a website, the more we turn away regular humans as well. Here's a short and non-exhaustive list of techinques:

1. User Agent Filtering
2. CAPTCHA solving
3. Rate Limiting
4. Proof of work
5. Identification
6. Paywall

### User Agent Filtering

When a person/bot requests a page from a website, the HTTP header of the request has a field called `User-Agent`.  This is to denote the type of client that the requester is using. For example, when I visited a website just now, I sent the user agent `Mozilla/5.0 (X11; Linux x86_64; rv:139.0) Gecko/20100101 Firefox/139.0`.

Filtering based on this string is the easiest technique to employ and also has a low chance of impacting regular humans visiting the website. [RFC 9309 Robots Exclusion Protocol](https://www.rfc-editor.org/rfc/rfc9309.html), more commonly known as `robots.txt`, is the most common way of implementing this technique.

How it works is that you create a file named `robots.txt` at the root directory of your website and write a set of rules that different robots *should* follow. Here's an example from [Google's search documentation](https://developers.google.com/search/docs/crawling-indexing/robots/create-robots-txt):

```txt
User-agent: Googlebot
Disallow: /nogooglebot/

User-agent: *
Allow: /

Sitemap: https://www.example.com/sitemap.xml
```

The `*` here is the Klenne star which means that it can match any string. Before the bot requests a page, the idea is that they first request this `robots.txt` file, find the rules that match their user agent, and follow it's instructions.

As you might imagine, not everyone writes scrapers that follow these rules. This depends on how well-written the bot was and how considerate the developer is. An alternative to this approach is to block the request at the web server. For example, here's how you would do that using `nginx`

```nginx
if ($http_user_agent = "Googlebot"){
    return 403;
}
```

This returns an empty response with the HTTP code `403 Forbidden`.

The downside to this approach is that it's easy to pretend that you have a different user agent. For example on my machine, the user agent set by `curl` is `curl/8.9.1`. However, I can use the same user agent as my browser by adding a flag:

```bash
curl --user-agent "Mozilla/5.0 (X11; Linux x86_64; rv:139.0) Gecko/20100101 Firefox/139.0" https://brandonrozek.com
```

### CAPTCHA Solving
The Completely Automated Public Turing test to tell Computers and Humans Apart (CAPTCHA) is a challenge-response approach to dealing with bots. The idea is that the webserver would present some sort of challenge that is supposedly hard for computers to solve but easy for humans. The human responds to the challenge and then is granted access to the website.

In the paper "Recent advances of Captcha security analysis: a short literature review" by Nghia Trong Dinh and Vinh Truong Hoang, they show that for the majority of CAPTCHA systems, bots are successful at solving them over 50% of the time. Specifically, the best bots are able to solve Google's image-based CAPTCHAs with 70.78% accuracy.

Unfortunately[^2] the success rate of bots are bound to improve over time. Additionally, CAPTCHA systems are annoying to humans. For example, when I use a VPN, I don't bother with Google search since I don't want to select pictures of stairs, fire hydrants, or crosswalks 10 times before being granted a search query.

[^2]: Or fortunately, if we want to get closer to AGI

### Rate Limiting

Computers are inherently faster than us. In the paper "How many words do we read per minute? A review and meta-analysis of reading rate" by Marc Brysbaert, he writes that the average human adult reads 238 words per minute of non-fiction silently. Thus, it would take a human on average almost 11 hours to read all my prior blog posts (assuming they don't get tired or distracted). Meanwhile a bot can scrape this site in under a minute.

From this insight, one technique is to limit the number of requests that an IP address can make at any given time. This is formally known as *rate limiting*.

It sounds simple in concept but can be difficult to implement without impacting user experience. How many requests is a human reasonably allowed to make in a minute? Human traffic is typically bursty, where a page load can request many different files (CSS, JS, media) in a short period of time.  How quick can I expect someone to reasonably click around my website? If this isn't dialed in properly, then rate limiting can cause frustration with your visitors.

I'm also unsure how successful this is against the LLM web scrapers. Nowadays there are bot farms where they each have their own IP address. It's difficult to determine whether a request is from a human visitor or part of a larger bot collection network.

### Proof of work

We talked about how CAPTCHAs are difficult for computers but easy for humans. Proof of work is difficult for both computers and humans. This helps reduce the number of scrapers by making it *costly* to request resources from the website. By making the web browser solve some proof of work challenge (usually involving hash functions), the request consumes additional CPU cycles and takes additional time. 

Similar to rate limiting, how *difficult* you make the problem has a direct impact on user experience. The more difficult, the longer it'll take for the web browser to solve it. This will deter more bots, but after a few seconds will also deter human visitors. [According to a study performed by Google and SOASTA Research in 2017](https://web.archive.org/web/20250121155519/https://www.thinkwithgoogle.com/marketing-strategies/app-and-mobile/page-load-time-statistics/), if a user has to wait 3 seconds instead of 1 second, then the probability that they *bounce* (leave the page) increases by 32%.

Recently, open-source projects [Anubis](https://anubis.techaro.lol/) and [go-away](https://git.gammaspectra.live/git/go-away) gained popularity for making it easy to implement this technique. It's popular for git forges like [sourcehut's](https://git.sr.ht/) as scraping those incurs a lot of CPU cycles in traversing git repositories.

### Identification

Another tactic is to ask the requester to provide some information that a human would likely have but a bot less so. Examples include email addresses, phone number, government ID, etc. Of course, a bot can supply false information, but as with the other techinques this adds an additional barrier. Watch out for the [fake phone numbers](https://gregoryhammond.ca/blog/never-to-connect-phone-numbers-a-project/).

### Paywall

Lastly, you can require users to pay to see the contents of your website. This is popular with news organizations where they ask you to pay for a subscription in order to see content. This ties in well with the previous tactic, because if the user pays for a subscription, then you likely have a lot of identifying information about that user.

Another interesting idea that I haven't seen widely implemented is requiring some amount of money per interaction. This can be in the form of the [Web Monetization API](https://webmonetization.org/) or via cryptocurrency like Bitcoin on the [Lightning network](https://lightning.network/). [Stacker news](https://stacker.news/) is an example of a Reddit-like platform where users need to pay a small fee in order to upvote a post. The idea is to make it cheap for a human to do on a small scale (like 1 cent per up-vote), but expensive for a bot to do at scale.

### Conclusion

We're in a special time period where everyone is fighting to become the top AI company. Long term, I feel that the scraper activity will die down. Similar to how there weren't as many web search scrapers out there.

In the meantime, these are multiple techniques to consider if your website is suffering under heavy load. As for myself, I don't currently implement any of these as my website is mostly static and I haven't noticed my servers being overloaded.

However if you do, I urge you to exercise some caution. For the most part, we share on the web for information to flow freely, and if we're not careful we may drive people away.
