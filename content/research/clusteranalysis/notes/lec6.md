---
title: Agglomerative Methods
showthedate: false
math: true
---

## Single Linkage

First let us consider the single linkage (nearest neighbor) approach. The clusters can be found through the following algorithm

1. Find the smallest non-zero distance
2. Group the two objects together as a cluster
3. Recompute the distances in the matrix by taking the minimum distances
   - Cluster a,b -> c = min(d(a, c), d(b, c))

Single linkage can operate directly on a proximity matrix, the actual data is not required.

A wonderful visual representation can be found in Everitt Section 4.2

## Centroid Clustering

This is another criterion measure that requires both the data and proximity matrix. These are the following steps of the algorithm. Requires Euclidean distance measure to preserve geometric correctness

1. Find the smallest non-zero distance
2. Group the two objects together as a cluster
3. Recompute the distances by taking the mean of the clustered observations and computing the distances between all of the observations
   - Cluster a,b -> c = d(mean(a, b), c)

## Complete Linkage

This is like Single Linkage, except now we're taking the farthest distance. The algorithm can be adjusted to the following

1. Find the smallest non-zero distance
2. Group the two objects together as a cluster
3. Recompute the distances in the matrix by taking the maximum distances
   - Cluster a,b -> c = max(d(a, c), d(b, c))

##Unweighted Pair-Group Method using the Average Approach (UPGMA)

In this criterion, we are no longer summarizing each cluster before taking distances, but instead comparing each observation in the cluster to the outside point and taking the average

1. Find the smallest non-zero distance
2. Group the two objects together as a cluster
3. Recompute the distances in the matrix by taking the mean 
   - Cluster A: a,b -> c = $mean_{i = 0}(d(A_i, c))$

## Median Linkage

This approach is similar to the UPGMA approach, except now we're taking the median instead of the mean

1. Find the smallest non-zero distance
2. Group the two objects together as a cluster
3. Recompute the distances in the matrix by taking the median
   - Cluster A: a,b -> c = $median_{i = 0}{(d(A_i, c))}$

## Ward Linkage

This one I didn't look too far into but here's the description: With Ward's linkage method, the distance between two clusters is the sum  of squared deviations from points to centroids. The objective of Ward's  linkage is to minimize the within-cluster sum of squares.

## When to use different Linkage Types?

According to the following two stack overflow posts: https://stats.stackexchange.com/questions/195446/choosing-the-right-linkage-method-for-hierarchical-clustering and https://stats.stackexchange.com/questions/195456/how-to-select-a-clustering-method-how-to-validate-a-cluster-solution-to-warran/195481#195481

These are the following ways you can justify a linkage type.

**Cluster metaphor**. *"I preferred this method because it constitutes clusters such (or such a way) which meets with my concept of a cluster in my particular project."*

**Data/method assumptions**. *"I preferred this method because my data nature or format predispose to it."*

**Internal validity**. *"I preferred this method because it gave me most clear-cut, tight-and-isolated clusters."* 

**External validity**. *"I preferred this method because it gave me clusters which differ by their background or clusters which match with the true ones I know."*

**Cross-validity**. *"I preferred this method because it is giving me very similar clusters on equivalent samples of the data or extrapolates well onto such samples."*

**Interpretation**. *"I preferred this method because it gave me clusters which, explained, are most persuasive that there is meaning in the world."*

### Cluster Metaphors

Let us explore the idea of cluster metaphors now.

**Single Linkage** or **Nearest Neighbor** is a *spectrum* or *chain*.

Since single linkage joins clusters by the shortest link between them, the technique cannot discern poorly separated clusters. On the other hand, single linkage is one of the few clustering methods that can delineate nonelipsodial clusters.

**Complete Linkage** or **Farthest Neighbor** is a *circle*.

 **Between-Group Average linkage** (UPGMA) is a united *class

**Centroid method** (UPGMC) is *proximity of platforms* (commonly used in politics)

## Dendrograms

A **dendrogram** is a tree diagram frequently used to illustrate the arrangement of the clusters produced by hierarchical clustering. It shows how different clusters are formed at different distance groupings.
