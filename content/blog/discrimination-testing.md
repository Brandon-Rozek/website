---
title: "Can you tell the difference? A quick look into discrimination testing."
date: 2026-05-24T15:32:35-04:00
draft: false
tags: []
math: false
medium_enabled: false
---

A few month's ago, Brad Reese, the grandson of the founder of the Reese's company, called the company out for [swapping out the chocolate and peanut butter in some of their products](https://www.linkedin.com/posts/bradreesecom_reeses-brandstewardship-corporateaccountability-activity-7428545969430016001-zOL7/). The newer ingredients "chocolate candy" and "peanut butter creme" are only imitations.

> But today, REESE'S  identity is being rewritten, not by storytellers, but by formulation  decisions that replace Milk Chocolate with compound coatings and Peanut  Butter with peanut‑butter‑style crèmes across multiple REESE’S products.
>
> \- Brad Reese

Jonathan Deutsch over at the Conversation wrote that product reformulations in foods are common and most of the time [we don't even notice](https://theconversation.com/controversy-over-reeses-ingredients-reveals-standard-food-industry-practices-most-consumers-never-notice-276808). This along with shrinking the size of the product are the two main approaches companies use to reduce costs. 

## Discrimination Testing for Food

So how can companies be confident that few will notice? That's where discrimination testing comes in. From my research and what Jonathan shared, the most common type of discrimination test used in the food science industry is the [triangle test](https://www.sensorysociety.org/knowledge/sspwiki/Pages/Triangle%20Test.aspx).

In this test, the participant is given three products (A, B, C) and are told that only one of them is different. If the participant is able to correctly identify which one, then there's evidence that the average person can do the same. The probability that a random guess is correct is 1/3. Therefore, it's not sufficient to ask a single person and instead we need many participants to obtain statistical significance.

## Discrimination Testing for Audio

A few weeks later, I read Andreas' post on [telling the difference between compressed and uncompressed audio](https://82mhz.net/posts/2026/03/can-i-hear-a-difference-between-mp3s-and-uncompressed-audio/). This made me curious on what discrimination tests are commonly used in the audio setting. However, this was difficult for me to search for. 

In the food setting, I've found multiple presentations and publications by the [Society of Sensory Professionals](https://www.sensorysociety.org/Pages/default.aspx) and the [Institute for Perception](https://www.ifpress.com/). I wasn't able to easily find any groups focused on the audio setting. As our last resort, we'll trust Wikipedia and say that [ABX Testing](https://en.wikipedia.org/wiki/ABX_test) is commonly used.

In ABX testing, the participant is told which sample is A and which sample is B. The task is then to guess whether X = A or X = B. What's important here is that the participant knows that A is not equal to B. Hence, the participant is provided with more information than in the triangle test setting.

For our audio example, we can say that A is the uncompressed audio, B is the compressed audio, and the task is to guess which X is. The probability of a random guess being correct in this test is 1/2 which is much higher than the triangle test.

Honestly, I can't figure out why this test is more common than the others. If you're a perception researcher and have some insight, please get in touch.

One thing to note about discrimination testing is that it only tells us if there is a perceptible difference. When comparing compression algorithms, we often want feedback on the perceived quality differences. I didn't look into this area much, but if you're interested then the [MUSHRA](https://en.wikipedia.org/wiki/MUSHRA) method seems to be a good starting point.

## The Tip of the Iceburg

As you might have noticed by now, I'm not a perception researcher. There are a lot of discrimination tests out there and many folks are working on new ideas in this space. To close out this quick introduction,  I'll share two other approaches that I came across when writing this post. 

First, there's the [two out of five test](https://www.sensorysociety.org/knowledge/sspwiki/Pages/Two-out-of-five%20Test.aspx). It's similar to the triangle test where the participant is given no labels but this time they're asked to identify the two that are unlike the other three. The probability of randomly guessing correctly in this test is 1/10 which is by far the lowest out of the approaches I shared in this post. The downside to this test is that the participant has to sample five items which might cause sensory fatigue and it's easy to give [incorrect instructions](https://onlinelibrary.wiley.com/doi/10.1111/joss.12044).

[Tetrad testing](https://www.ifpress.com/tr-15-1) is when the participant is given 4 samples and are asked to pair up the equivalent ones. The probability of guessing correctly is equivalent to that of the triangle test, but Ennis and Jesionka show that in some cases the Tetrad test [requires one third the number of participants as that required by the triangle test](https://doi.org/10.1111/j.1745-459X.2011.00353.x). The Institute for Perception released a techincal report arguing for the switch to Tetrad testing in order to [reduce costs](https://www.ifpress.com/tr-15-1). There's even a fun presentation publicly available by Hannah Lemar showing the suitability of the Tetrad test in the [brewing industry](https://www.asbcnet.org/events/archives/2016/proceedings/Documents/8_Lemar.pdf). 

What do you think, is it important to perceive the original, or does an imitation work for you? For me, I don't mind listening to compressed audio at all. I like to think, however, that I'm aware of what I'm eating.
