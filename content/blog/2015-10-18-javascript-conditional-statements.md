---
id: 344
title: Javascript Conditional Statements
date: 2015-10-18T18:30:21+00:00
author: Brandon Rozek
layout: post
guid: https://brandonrozek.com/?p=344
permalink: /2015/10/javascript-conditional-statements/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"72ac61ee8d04";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:79:"https://medium.com/@brandonrozek/javascript-conditional-statements-72ac61ee8d04";}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"72ac61ee8d04";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:79:"https://medium.com/@brandonrozek/javascript-conditional-statements-72ac61ee8d04";}'
dsq_thread_id:
  - "4237729275"
  - "4237729275"
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
tumblr_post_id:
  - "135657634939"
  - "135657634939"
kind:
  - article
---
Javascript, like most other programming languages, include ways to run blocks of code when something meets a condition. Here, I will describe the most common ways to do so.

<!--more-->

This post is part of my lecture series for Math I/O. There is no pre-reading for this lecture.

### <a href="#if-statement" name="if-statement"></a>If Statement {#if-statement}

To run a block of code when a condition is true, use an <code class="language-javascript">if</code> statement.

<pre><code class="language-javascript">    if (condition) {
        doSomething();
    }
</code></pre>

You can also run a block of code when a condition is false using the <code class="language-javascript">else</code> statement.

<pre><code class="language-javascript">    if (condition) {
        doSomething();
    } else {
        doSomethingElse();
    }
</code></pre>

### <a href="#switch-statement" name="switch-statement"></a>Switch statement {#switch-statement}

If you want to check a variable for **equality** against multiple different cases, use a <code class="language-javascript">switch</code> statement.

<pre><code class="language-javascript">    switch (variable) {
        case condition1:
            doSomething();
            break;
        case condition2:
            doSomethingElse();
            break;
        default:
            doSomethingCompletelyDifferent();
            break;
    }
</code></pre>

The default statement runs when the variable doesn’t equal any of the cases.

### <a href="#while-loop" name="while-loop"></a>While loop {#while-loop}

To run a block of code over and over again until a condition is false, use a <code class="language-javascript">while</code> loop.

<pre><code class="language-javascript">    while (condition) {
        doSomething();
    }
</code></pre>

Don’t forget to include something in the loop that will eventually make the condition <code class="language-javascript">false</code>, otherwise you run into an infinite loop. (Which is a loop that never stops repeating itself; most likely crashing your browser)

### <a href="#for-loop" name="for-loop"></a>For loop {#for-loop}

If you want to run something a certain amount of times, use a &#8220;<code class="language-javascript">for"</code> loop. For loops can be broken down into three components: an initiating statement, a condition, and a statement that runs after every loop.

<pre><code class="language-javascript">    for (var i = 0; i &lt; 5; i++) {
        doSomething();
    }
</code></pre>

Here you have the initiating statement of <code class="language-javascript">var i = 0</code>. From there you check, is <code class="language-javascript">i</code> less than 5? Yes, so then we <code class="language-javascript">doSomething();</code>. After we <code class="language-javascript">doSomething();</code>, we add 1 to <code class="language-javascript">i</code>. Now <code class="language-javascript">i</code> equals 2. Is <code class="language-javascript">i</code> still less than 5? Yes, so we <code class="language-javascript">doSomething();</code>. Then we add 1 to <code class="language-javascript">i</code> again. This loop will keep happening until <code class="language-javascript">i</code> is not less than 5.

### <a href="#conclusion" name="conclusion"></a>Conclusion {#conclusion}

Having different control/conditional statements helps keep the state of any application you’re making. Did the user say not to notify them? Then don’t, otherwise (else) notify them. That’s all I have to say for this week. Hope this post helps you get a little more used to this big world called programming.

<pre><code class="language-javascript">    if (youLikeThisPost) {
        console.log("Come back next week! :)");
    } else {
        console.log("Aww that's okay, you should give me another chance next week :)");
    }
</code></pre>

I recommend that you look at different perspectives of the same concepts. WebCheatSheet.com has a similar post to mine, check out what they had to say [here](http://webcheatsheet.com/javascript/if_else_switch.php).