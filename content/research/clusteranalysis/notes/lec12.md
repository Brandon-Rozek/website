---
title: Introduction to Density Based Clustering
showthedate: false
math: true
---

In density-based clustering, clusters are defined as areas of higher density than the remainder of the data sets. Objects in more sparse areas are considered to be outliers or border points. This helps discover clusters of arbitrary shape.

## DBSCAN

Given a set of points in space, it groups together points that are closely packed together while marking points that lie alone in low-density regions as outliers.

### Preliminary Information

- A point $p$ is a core point if at least k (often referred to as minPts) are within $\epsilon$ of it. Those points are said to be *directly reachable* from $p$.
- A point $q$ is directly reachable from $p$ if point $q$ is within distance $\epsilon$ from point $p$ and $p$ must be a core point
- A point $q$ is reachable from $p$ if there is a path $p_1, \dots, p_n$ with $p_1 = p$ and $p_n = q$ where each $p_{i + 1}$ is directly reachable from $p_i$. (All points on the path must be core points, with the possible exception of $q$)
- All points not reachable from any other points are outliers

Non core points can be part of a cluster, but they form its "edge", since they cannot be used to reach more points.

Reachability is not a symmetric relation since, by definition, no point may be reachable from a non-core point, regardless of distance. 

Two points $p$ and $q$ are density-connected if there is a point $o$ such that both $p$ and $q$ are reachable from $o$. Density-connectedness is symmetric.

A cluster then satisfies two properties:

1. All points within the cluster are mutually density-connected
2. If a point is density-reachable from any point of the cluster, it is part of the cluster as well.


### Algorithm

1. Find the $\epsilon$ neighbors of every point, and identify the core points with more than $k$ neighbors.
2. Find the connected components of *core* points on the neighborhood graph, ignoring all non-core points.
3. Assign each non-core point to a nearby cluster if the cluster is an $\epsilon$ (eps) neighbor, otherwise assign it to noise.

### Advantages

- Does not require one to specify the number of clusters in the data
- Can find arbitrarily shaped clusters
- Has a notion of noise and is robust to outliers

### Disadvantages

- Not entirely deterministic: border points that are reachable from more than one cluster can be part of either cluster.
- The quality to DBSCAN depends on the distance measure used.
- Cannot cluster data sets well with large differences in densities.

### Rule of Thumbs for parameters

$k$: $k$ must be larger than $(D + 1)$ where $D$ is the number of dimensions in the dataset. Normally $k$ is chosen to be twice the number of dimensions.

$\epsilon$: Ideally the $k^{th}$ nearest neighbors are at roughly the same distance. Plot the sorted distance of every point to it's $k^{th}$ nearest neighbor



Example of Run Through

https://www.cse.buffalo.edu/~jing/cse601/fa12/materials/clustering_density.pdf
