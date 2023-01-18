---
id: 2089
title: Approximate Pi using a Monte Carlo Simulation
date: 2017-03-14T05:31:21+00:00
author: Brandon Rozek
layout: post
guid: https://brandonrozek.com/?p=2089
aliases:
    - /2017/03/monte-carlo-pi/
permalink: /2017/03/monte-carlo-pi/
medium_post:
  - 'O:11:"Medium_Post":11:{s:16:"author_image_url";N;s:10:"author_url";N;s:11:"byline_name";N;s:12:"byline_email";N;s:10:"cross_link";N;s:2:"id";N;s:21:"follower_notification";N;s:7:"license";N;s:14:"publication_id";N;s:6:"status";N;s:3:"url";N;}'
tumblr_post_id:
  - "158383170019"
mf2_syndicate-to:
  - 'a:1:{i:0;s:22:"bridgy-publish_twitter";}'
mf2_cite:
  - 'a:4:{s:9:"published";s:25:"0000-01-01T00:00:00+00:00";s:7:"updated";s:25:"0000-01-01T00:00:00+00:00";s:8:"category";a:1:{i:0;s:0:"";}s:6:"author";a:0:{}}'
mf2_syndication:
  - 'a:1:{i:0;s:60:"https://twitter.com/B_RozekJournal/status/841522141346570244";}'
format: aside
kind:
  - note
tags: ["Math", "Java"]
math: true
---
Using Monte Carlo methods, we can create a simulation that approximates pi. In this post, we will go over the math behind the approximation and the code.

<!--more-->

## The Math

Pi is a mathematical constant consisting of the ratio between the circumfrence of a circle and it&#8217;s diameter.

The circumfrence of the circle is defined to be $$ C = 2\pi r$$ while the diameter of the circle is $$d = 2r$$

Take the ratio between the two and you get $$\frac{2\pi r}{2r} = \pi$$

Now let us consider the area of a circle. One can derive the area of a circle by taking the integral of the circumfrence with respect to it&#8217;s radius $$ A_{circle} = \int{(2\pi r) dr} = \pi r^2 $$

Let us simplify the formula more by setting the radius equal to one. $$A_{circle} = \pi$$

Now consider only the first quadrant of the circle. Since our circle is centered at the origin and all the points on the circumfrence is equidistant from the center, our area is now $$A_{circle} = \frac{1}{4} \pi$$

And bound the quarter-circle in a 1&#215;1 box with an area of $$A_{square} = 1^2 = 1$$

Notice that the ratio between the circle and the square is a quarter of pi $$\frac{A\_{circle}}{A\_{square}} = \frac{\frac{1}{4} \pi}{1} = \frac{1}{4} \pi$$

## Simulation and Statisitcs

The formula for a circle centered at the origin with radius one is $$x^2 + y^2 = 1$$

Let us focus again on the first quadrent, and do a Monte Carlo simulation to find the area of the quarter-circle

![](https://brandonrozek.com/wp-content/uploads/2017/03/circlefilled.png) 

We can do this by what is called the dart board method. We generate a random x and y between 0 and 1. If it satisfies the inequality $$x^2 + y^2 \leq 1$$ then it counts as being inside the circle, if not then it lies outside the circle.

That point will count as an really small area. The point will always be inside the square but may sometimes be inside the circle. Running the simulations a large number of times allows us to add up all the tiny little areas that make up the circle and the square.

To add up these small areas we need to make an assumption. The assumption is that the variance of all the little Monte Carlo trials are the same. Since we are using a psuedo-random number generator, it is safe to assume it is met.

This will allow us to perform a pooled empiricle probability on the simulations to sum up the areas.

Meaning the area of the circle will be the number of times that the inequality was satisfied $$A_{circle} = \\# Successes$$

And the area of the square will be the number of times the simulation was run, since the random numbers generated will always be between 0 and 1 $A_{square} = \\# Trials$

Recall that taking the ratio of the area of the circle and the area of the square is a fourth of pi. $$\frac{\frac{1}{4} \pi}{1} = \frac{1}{4} \pi$$

Multiply this number by 4 and you get the value for pi.

This tells us that four times the probability that the randomly generated point is in the circle is equal to pi.

$$\pi = 4 * (Probability\ of\ being\ inside\ circle) = 4 * \frac{\\# Success}{\\# Trials} = 4 * \frac{A\_{circle}}{A\_{square}}$$

## Implementation

For the Monte Carlo simulation I used Java. The BigDecimal implementation was used so that there wouldn&#8217;t be any issue with integer size limits

```java
/** Calculates Pi
  * @author Brandon Rozek
*/
// Big Integers are used so we don't run into the integer size limit
import java.math.BigInteger;
import java.math.BigDecimal;
class MonteCarloPi {
        public static void main(String[] args) {

                BigInteger successes = BigInteger.ZERO;
                BigInteger trials = BigInteger.ZERO;
```

For this simulation, we will run 1,000,000,000 trials

```java
BigInteger numTrials = new BigInteger("1000000000");
/*
    Monte Carlo Simulation
        Generate a random point 0 &lt;= x &lt; 1 and 0 &lt;= y &lt; 1
        If the generated point satisfies x^2 + x^2 &lt; 1
           Count as a success
        Keep track of the number of trials and successes
*/
for (; trials.compareTo(numTrials) &lt; 0; trials = trials.add(BigInteger.ONE)) {
    double randomX = Math.random();
    double randomY = Math.random();
    if (Math.pow(randomX, 2) + Math.pow(randomY, 2) &lt; 1) {
        successes = successes.add(BigInteger.ONE);
    }
}
```

And then we finalize it with a quick calculation of pi

```java
// (Number of successes) / (Number of trials) * 4 gives the approximation for pi
BigDecimal pi = new BigDecimal(successes)
                       .divide(new BigDecimal(trials))
                       .multiply(new BigDecimal("4"));
System.out.println("The calculated value of pi is: " + pi);
}}
```

## Conclusion

We found an approximation of pi using the Monte Carlo methods! I find that really awesome, however, there are some concerns I have with this approach.

1) We don&#8217;t keep track of double counting. One possible solution for this is increasing the radius and bounding box appropriately so that the probability of double counting is low.

2) Speed. The more trials you ask it to run, the longer it takes to perform all of the simulations. One possible way around this is to write a parrallel version of this code. That&#8217;s possible because of the equal variance that we spoke of earlier. Pooling the successses and trials will still result in a good approximation.
