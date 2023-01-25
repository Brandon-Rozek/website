---
id: 398
title: Math with Fractions.js
date: 2015-11-15T12:46:14+00:00
author: Brandon Rozek
aliases:
    - /2015/11/fractions-js/
permalink: /2015/11/fractions-js/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"dd3b15d9d3c9";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:68:"https://medium.com/@brandonrozek/math-with-fractions-js-dd3b15d9d3c9";}'
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";s:74:"https://cdn-images-1.medium.com/fit/c/200/200/1*dmbNkD5D-u45r44go_cf0g.png";s:10:"author_url";s:32:"https://medium.com/@brandonrozek";s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";s:2:"no";s:2:"id";s:12:"dd3b15d9d3c9";s:21:"follower_notification";s:2:"no";s:7:"license";s:19:"all-rights-reserved";s:14:"publication_id";s:2:"-1";s:6:"status";s:6:"public";s:3:"url";s:68:"https://medium.com/@brandonrozek/math-with-fractions-js-dd3b15d9d3c9";}'
mf2_cite:
  - 'a:1:{s:6:"author";a:0:{}}'
  - 'a:1:{s:6:"author";a:0:{}}'
tags: ["JS"]
---
Last week I published my first library over on Github called [Fractions.js](https://github.com/brandonrozek/Fractions.js). Fractions.js is a library to help avoid the [mathmatetical errors](http://floating-point-gui.de/) in floating point arithmetic. What do you mean by floating point artihmetic errors? Here is an example: <code class="language-javascript">.1 * .2</code> outputs <code class="language-javascript">0.020000000000000004</code> even though the correct answer is <code class="language-javascript">.02</code>

<!--more-->

## <a href="#purpose" name="purpose"></a>Purpose {#purpose}

My team and I are currently working on a new game for Math I/O. One of the levels is testing whether the player can add, subtract, multiply, and divide fractions correctly. I didn’t want to implement a solution where we check if the input entered is within a range of the answer. So I asked the team, how do you add, subtract, multiply, and divide fractions in your head? As we were working through it together, I realized that this is a common problem over at Math I/O. So I decided to make a library dedicated to this.

## <a href="#how-it-works" name="how-it-works"></a>How it works {#how-it-works}

I broke up each fraction into two things, a numerator and a denominator. With these two numbers, I can figure out all of the most common operations.

### <a href="#addition" name="addition"></a>Addition {#addition}

For addition, if two fractions have the same denominator, then you just need to add the numerators.

    1/3 + 1/3 = 2/3


If not, then you need to change it to have a common denominator. We can do this by multiply each fractions numerator and denominator by the other fractions denominator.

    1/2 + 1/3 = (1 * 3)/ (2 * 3) + (1 * 2)/ (2 * 3) = 3/6 + 2/6 = 5/6


### <a href="#subtraction" name="subtraction"></a>Subtraction {#subtraction}

Works the same as addition, except the second fraction is subtracted (taken away) from the first.

### <a href="#multiplication" name="multiplication"></a>Multiplication {#multiplication}

To multiply two fractions, just multiply the numerators by each other, and the denominators by each other.

    2/3 * 1/2 = 2/6


### <a href="#division" name="division"></a>Division {#division}

Treated similar to multiplication since dividing a number is the same thing as multiplying by it’s [reciprocal](https://www.mathsisfun.com/reciprocal.html).

    1 / (1 / 2) = 1 * 2 = 2


### <a href="#simplification" name="simplification"></a>Simplification {#simplification}

Sometimes with the operations above, it’ll produce fractions in an unsimplified form. To avoid any confusion, I created a simplify function. It was challanging trying to figure out a way to code this. While I was browsing around for an implementation, I knocked into Euclider’s algorithm for finding the greatest common factor. Straight from the [Wikipedia article](https://en.wikipedia.org/wiki/Euclidean_algorithm) (where a is greater than b):


    function gcd(a, b)
        while b ≠ 0
           t := b;
           b := a mod b;
           a := t;
        return a;


I can then simplify the fraction by dividing the numerator and denominator by the greatest common factor.

## <a href="#the-api" name="the-api"></a>The API {#the-api}

I decided to provide as much flexibility as I can in the API. You have several ways to create a new Fraction.

<pre><code class="language-javascript">
var oneHalf = new Fraction(1,2);
var oneHalf = new Fraction(.5);
var oneHalf = new Fraction("1/2");
var oneHalf = new Fraction("1", "2")
</code></pre>

All of these results will return a Fraction with a numerator of <code class="language-javascript">1</code> and a denominator of <code class="language-javascript">2</code>. You also have two different ways to do the most common operations.

<pre><code class="language-javascript">
var fiveThirds = Fraction.add("1/3", "4/3");
var fiveThirds = new Fraction("1/3").add("4/3");
</code></pre>

The second style came from how jQuery implements it’s library. That way you can chain operations.

<pre><code class="language-javascript">
new Fraction("1/2").add("2/3").divide("5/6").subtract("7/8").multiply("6/5").toString()
</code></pre>

Outputs <code class="language-javascript">'63/100'</code> This is accomplished in the code through [prototypes](http://javascriptissexy.com/javascript-prototype-in-plain-detailed-language/).

<pre><code class="language-javascript">
Fraction.add = function(frac1, frac2) {
    Fraction.correctArgumentLength(2, arguments.length);
    frac1 = Fraction.toFraction(frac1)
    frac2 = Fraction.toFraction(frac2)

    var newFrac = frac1;
    newFrac.numerator = frac1.numerator * frac2.denominator + frac1.denominator * frac2.numerator;
    newFrac.denominator = frac1.denominator * frac2.denominator;
    return Fraction.simplify(newFrac);
}
Fraction.prototype.add = function(frac) {
    Fraction.correctArgumentLength(1, arguments.length);
    return Fraction.change(this, Fraction.add(this, frac));
}
</code></pre>

In the code, the add prototype calls the Fraction.add function within it to avoid code duplication.

## <a href="#conclusion" name="conclusion"></a>Conclusion {#conclusion}

After I coded this up, I looked online for different implementations and found [fraction.js](https://github.com/ekg/fraction.js) by [Erik Garrison](http://hypervolu.me/~erik/). It’s important to look at different implementations and see which matches your needs better. This post isn’t meant to go fully into detail of the library. To know what else the library can do, visit the [readme page](https://github.com/brandonrozek/Fractions.js/blob/master/README.md). If you’re curious in how it’s implemented, check out the [code](https://github.com/brandonrozek/Fractions.js/blob/master/Fraction.js). [Email me](mailto:brozek@brandonrozek.com) if you have any questions/criticisms 🙂