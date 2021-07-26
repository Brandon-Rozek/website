---
title: CURE and TSNE
showthedate: false
math: true
---

##Clustering Using Representatives (CURE)

Clustering using Representatives is a Hierarchical clustering technique in which you can represent a cluster using a **set** of well-scattered representative points.

This algorithm has a parameter $\alpha$ which defines the factor of the points in which to shrink towards the centroid.

CURE is known to be robust to outliers and able to identify clusters that have a **non-spherical** shape and size variance.

The clusters with the closest pair of representatives are the clusters that are merged at each step of CURE's algorithm.

This algorithm cannot be directly applied to large datasets due to high runtime complexity. Several enhancements were added to address this requirement

- Random sampling: This involves a trade off between accuracy and efficiency. One would hope that the random sample they obtain is representative of the population
- Partitioning: The idea is to partition the sample space into $p$ partitions

Youtube Video: https://www.youtube.com/watch?v=JrOJspZ1CUw

Steps

1. Pick a random sample of points that fit in main memory
2. Cluster sample points hierarchically to create the initial clusters
3. Pick representative point**s**
   1. For each cluster, pick $k$ representative points, as dispersed as possible
   2. Move each representative points to a fixed fraction $\alpha$ toward the centroid of the cluster
4. Rescan the whole dataset and visit each point $p$ in the data set
5. Place it in the "closest cluster"
   1. Closest as in shortest distance among all the representative points.

## TSNE

TSNE allows us to reduce the dimensionality of a dataset to two which allows us to visualize the data.

It is able to do this since many real-world datasets have a low intrinsic dimensionality embedded within the high-dimensional space. 

Since the technique needs to conserve the structure of the data, two corresponding mapped points must be close to each other distance wise as well. Let $|x_i - x_j|$ be the Euclidean distance between two data points, and $|y_i - y_j|$ he distance between the map points. This conditional similarity between two data points is:
$$
p_{j|i} = \frac{exp(-|x_i-x_j|^2 / (2\sigma_i^2))}{\sum_{k \ne i}{exp(-|x_i-x_k|^2/(2\sigma_i^2))}}
$$
Where we are considering the **Gaussian distribution** surrounding the distance between $x_j$ from $x_i$ with a given variance $\sigma_i^2$. The variance is different for every point; it is chosen such that points in dense areas are given a smaller variance than points in sparse areas.

Now the similarity matrix for mapped points are
$$
q_{ij} = \frac{f(|x_i - x_j|)}{\sum_{k \ne i}{f(|x_i - x_k)}}
$$
Where $f(z) = \frac{1}{1 + z^2}$

This has the same idea as the conditional similarity between two data points, except this is based on the **Cauchy distribution**.

TSNE works at minimizing the Kullback-Leiber divergence between the two distributions $p_{ij}$ and $q_{ij}$
$$
KL(P || Q)  = \sum_{i,j}{p_{i,j} \log{\frac{p_{ij}}{q_{ij}}}}
$$
To minimize this score, gradient descent is typically performed
$$
\frac{\partial KL(P||Q)}{\partial y_i} = 4\sum_j{(p_{ij} - q_{ij})}
$$
