---
title: Cluster Tendency
showthedate: false
math: true
---

This is the assessment of the suitability of clustering. Cluster Tendency determines whether the data has any inherent grouping structure.

This is a hard task since there are so many different definitions of clusters (portioning, hierarchical, density, graph, etc.) Even after fixing a cluster type, this is still hard in defining an appropriate null model for a data set.

One way we can go about measuring cluster tendency is to compare the data against random data. On average, random data should not contain clusters.

There are some clusterability assessment methods such as Spatial histogram, distance distribution and Hopkins statistic.

## Hopkins Statistic

Let $X$ be the set of $n$ data points in $d$ dimensional space. Consider a random sample (without replacement) of $m << n$ data points. Also generate a set $Y$ of $m$ uniformly randomly distributed data points.

Now define two distance measures $u_i$ to be the distance of $y_i \in Y$ from its nearest neighbor in X and $w_i$ to be the distance of $x_i \in X$ from its nearest neighbor in X

We can then define Hopkins statistic as
$$
H = \frac{\sum_{i = 1}^m{u_i^d}}{\sum_{i = 1}^m{u_i^d} + \sum_{i =1}^m{w_i^d}}
$$

### Properties

With this definition, uniform random data should tend to have values near 0.5, and clustered data should tend to have values nearer to 1.

### Drawbacks

However, data containing a single Gaussian will also score close to one. As this statistic measures deviation from a uniform distribution. Making this statistic less useful in application as real data is usually not remotely uniform.



## Spatial Histogram Approach

For this method, I'm not too sure how this works, but here are some key points I found.

Divide each dimension in equal width bins, and count how many points lie in each of the bins and obtain the empirical joint probability mass function.

Do the same for the randomly sampled data

Finally compute how much they differ using the Kullback-Leibler (KL) divergence value. If it differs greatly than we can say that the data is clusterable.
