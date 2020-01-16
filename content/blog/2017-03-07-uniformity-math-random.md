---
id: 2095
title: Uniformity of Math.random()
date: 2017-03-07T21:50:52+00:00
author: Brandon Rozek
layout: post
guid: https://brandonrozek.com/?p=2095
permalink: /2017/03/uniformity-math-random/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
mf2_syndicate-to:
  - 'a:1:{i:0;s:4:"none";}'
mf2_cite:
  - 'a:4:{s:9:"published";s:25:"0000-01-01T00:00:00+00:00";s:7:"updated";s:25:"0000-01-01T00:00:00+00:00";s:8:"category";a:1:{i:0;s:0:"";}s:6:"author";a:0:{}}'
tumblr_post_id:
  - "158123669889"
format: aside
kind:
  - note
---
There are many cases where websites use random number generators to influence some sort of page behavior. One test to ensure the quality of a random number generator is to see if after many cases, the numbers produced follow a uniform distribution.

<!--more-->

Today, I will compare Internet Explorer 11, Chrome, and Firefox on a Windows 7 machine and report my results.

## Hypothesis

H0: The random numbers outputted follow the uniform distribution

HA: The random numbers outputted do not follow the uniform distribution

## Gathering Data

I wrote a small [website](http://share.zeropointshift.com/files/2017/03/random.html) and obtained my data by getting the CSV outputted when I use IE11, Firefox, and Chrome.

The website works by producing a random number using <code class='language-javascript'>Math.random()</code> between 1 and 1000 inclusive and calls the function 1,000,000 times. Storing it&#8217;s results in a file

This website produces a file with all the numbers separated by a comma. We want these commas to be replaced by newlines. To do so, we can run a simple command in the terminal

<pre class='language-bash'><code class='language-bash'>
grep -oE '[0-9]+' Random.csv &gt; Random_corrected.csv
</code></pre>

Do this with all three files and make sure to keep track of which is which.

Here are a copy of my files for [Firefox](https://brandonrozek.com/wp-content/uploads/2017/03/Firefox_corrected.csv), [Chrome](https://brandonrozek.com/wp-content/uploads/2017/03/Chrome_corrected-1.csv), and [IE11](https://brandonrozek.com/wp-content/uploads/2017/03/IE11_corrected.csv)

## Check Conditions

Since we&#8217;re interested in if the random values occur uniformly, we need to perform a Chi-Square test for Goodness of Fit. With every test comes some assumptions

<u>Counted Data Condition:</u> The data can be converted from quantatative to count data.

<u>Independence Assumption:</u> One random value does not affect another.

<u>Expected Cell Frequency Condition:</u> The expected counts are going to be 10000

Since all of the conditions are met, we can use the Chi-square test of Goodness of Fit

## Descriptive Statistics

For the rest of the article, we will use R for analysis. Looking at the histograms for the three browsers below. The random numbers all appear to occur uniformly

<pre class="language-R"><code class='language-R'>rm(list=ls())
chrome = read.csv("~/Chrome_corrected.csv", header = F)
firefox = read.csv("~/Firefox_corrected.csv", header = F)
ie11 = read.csv("~/IE11_corrected.csv", header = F)
</code></pre>

<pre class="language-R"><code class='language-R'>
hist(ie11$V1, main = "Distribution of Random Values for IE11", xlab = "Random Value")</code></pre>

![](https://brandonrozek.com/wp-content/uploads/2017/03/ie11hist.png) 

<pre class="language-R"><code class='language-R'>hist(firefox$V1, main = "Distribution of Random Values for Firefox", xlab = "Random Value")</code></pre>

![](https://brandonrozek.com/wp-content/uploads/2017/03/firefoxhist.png) 

<pre class="language-R"><code class='language-R'>hist(chrome$V1, main = "Distribution of Random Values for Chrome", xlab = "Random Value")</code></pre>

![](https://brandonrozek.com/wp-content/uploads/2017/03/chromehist.png) 

## Chi-Square Test

Before we run our test, we need to convert the quantatative data to count data by using the plyr package

<pre class="language-R"><code class='language-R'>#Transform to count data
library(plyr)
chrome_count = count(chrome)
firefox_count = count(firefox)
ie11_count = count(ie11)
</code></pre>

Run the tests

<pre class='language-R'><code class='language-R'>
# Chi-Square Test for Goodness-of-Fit
chrome_test = chisq.test(chrome_count$freq)
firefox_test = chisq.test(firefox_count$freq)
ie11_test = chisq.test(ie11_count$freq)

# Test results
chrome_test</code></pre>

As you can see in the test results below, we fail to reject the null hypothesis at a 5% significance level because all of the p-values are above 0.05.

    ## 
    ##  Chi-squared test for given probabilities
    ## 
    ## data:  chrome_count$freq
    ## X-squared = 101.67, df = 99, p-value = 0.4069

<pre class="r"><code>firefox_test</code></pre>

    ## 
    ##  Chi-squared test for given probabilities
    ## 
    ## data:  firefox_count$freq
    ## X-squared = 105.15, df = 99, p-value = 0.3172

<pre class="r"><code>ie11_test</code></pre>

    ## 
    ##  Chi-squared test for given probabilities
    ## 
    ## data:  ie11_count$freq
    ## X-squared = 78.285, df = 99, p-value = 0.9384

## Conclusion

At a 5% significance level, we fail to obtain enough evidence to suggest that the distribution of random number is not uniform. This is a good thing since it shows us that our random number generators give all numbers an equal chance of being represented. We can use <code class='language-javascript'>Math.random()</code> with ease of mind.