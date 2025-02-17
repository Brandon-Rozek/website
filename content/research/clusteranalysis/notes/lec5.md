---
title: Introduction to Connectivity Based Models
showthedate: false
---

Hierarchical algorithms combine observations to form clusters based on their distance.

## Connectivity Methods

Hierarchal Clustering techniques can be subdivided depending on the method of going about it.

First there are two different methods in forming the clusters *Agglomerative* and *Divisive*

**Agglomerative** is when you combine the n individuals into groups through each iteration

**Divisive** is when you are separating one giant group into finer groupings with each iteration.

Hierarchical methods are an irrevocable algorithm, once it joins or separates a grouping, it cannot be undone. As Kaufman and Rousseeuw (1990) colorfully comment: *"A hierarchical method suffers from the defect that it can never repair what was done in previous steps"*. 

It is the job of the statistician to decide when to stop the agglomerative or decisive algorithm, since having one giant cluster containing all observations or having each observation be a cluster isn't particularly useful.

At different distances, different clusters are formed and are more readily represented using a **dendrogram**. These algorithms do not provide a unique solution but rather provide an extensive hierarchy of clusters that merge or divide at different distances.

## Linkage Criterion

Apart from the method of forming clusters, the user also needs to decide on a linkage criterion to use. Meaning, how do you want to optimize your clusters.

Do you want to group based on the nearest points in each cluster? Nearest Neighbor Clustering

Or do you want to based on the farthest observations in each cluster? Farthest neighbor clustering.

![http://www.multid.se/genex/onlinehelp/clustering_distances.png](http://www.multid.se/genex/onlinehelp/clustering_distances.png)

## Shortcomings

This method is not very robust towards outliers, which will either show up as additional clusters or even cause other clusters to merge depending on the clustering method.

As we go through this section, we will go into detail about the different linkage criterion and other parameters of this model.
