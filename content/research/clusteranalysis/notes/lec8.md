---
title: Divisive Methods Pt 2.
showthedate: false
---

Recall in the previous section that we spoke about Monothetic and Polythetic methods. Monothetic methods only looks at a single variable at a time while Polythetic looks at multiple variables simultaneously. In this section, we will speak more about polythetic divisive methods.

## Polythetic Divisive Methods

Polythetic methods operate via a distance matrix.

This procedure avoids considering all possible splits by 

1. Finding the object that is furthest away from the others within a group and using that as a seed for a splinter group.
2. Each object is then considered for entry to that separate splinter group: any that are closer to the splinter group than the main group is moved to the splinter one. 
3. The step is then repeated.

This process has been developed into a program named `DIANA` (DIvisive ANAlysis Clustering) which is implemented in `R`.

### Similarities to Politics

This somewhat resembles a way a political party might split due to inner conflicts.

Firstly, the most discontented member leaves the party and starts a new one, and then some others follow him until a kind of equilibrium is attained.

## Methods for Large Data Sets

There are two common hierarchical methods used for large data sets `BIRCH` and `CURE`. Both of these algorithms employ a pre-clustering phase in where dense regions are summarized, the summaries being then clustered using a hierarchical method based on centroids.

### CURE

1. `CURE` starts with a random sample of points and represents clusters by a smaller number of points that capture the shape of the cluster
2. Which are then shrunk towards the centroid as to dampen the effect of the outliers
3. Hierarchical clustering then operates on the representative points

`CURE` has been shown to be able to cope with arbitrary-shaped clusters and in that respect may be superior to `BIRCH`, although it does require judgment as to the number of clusters and also a parameter which favors either more or less compact clusters.

## Revisiting Topics: Cluster Dissimilarity

In order to decide where clusters should be combined (for agglomerative), or where a cluster should be split (for divisive), a measure of dissimilarity between sets of observations is required.

In most methods of hierarchical clustering this is achieved by a use of an appropriate 

- Metric (a measure of distance between pairs of observations)
- Linkage Criterion (which specifies the dissimilarities of sets as functions of pairwise distances observations in the sets)

## Advantages of Hierarchical Clustering

- Any valid measure of distance measure can be used
- In most cases, the observations themselves are not required, just hte matrix of distances
  - This can have the advantage of only having to store a distance matrix in memory as opposed to a n-dimensional matrix.
