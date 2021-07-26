---
title: Why use different distance measures?
showthedate: false
---

I made an attempt to find out in what situations people use different distance measures. Looking around in the Internet usually produces the results "It depends on the problem" or "I typically just always use Euclidean"

Which as you might imagine, isn't a terribly useful answer. Since it doesn't give me any examples of which types of problems different distances solve.

Therefore, let's think about it in a different way. What properties do different distance measures have that make them desirable?

## Manhattan Advantages

- The gradient of this function has a constant magnitude. There's no power in the formula
- Unusual values affect distances on Euclidean more since the difference is squared

https://datascience.stackexchange.com/questions/20075/when-would-one-use-manhattan-distance-as-opposite-to-euclidean-distance



## Mahalanobis Advantages

Variables can be on different scales. The Mahalanobis formula has a built in variance-covariance matrix which allows you to rescale your variables to make distances of different variables more comparable.

https://stats.stackexchange.com/questions/50949/why-use-the-mahalanobis-distance#50956



## Euclidean Disadvantages

In higher dimensions, the points essentially become uniformly distant from one another. This is a problem observed in most distance metrics but it's more obvious with the Euclidean one.

https://stats.stackexchange.com/questions/99171/why-is-euclidean-distance-not-a-good-metric-in-high-dimensions/



Hopefully in this course, we'll discover more properties as to why it makes sense to use different distance measures since it can have a impact on how our clusters are formed.
