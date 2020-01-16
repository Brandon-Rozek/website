# Cluster Validation

There are multiple approaches to validating your cluster models

- Internal Evaluation: This is when you summarize the clustering into a single score. For example, minimizing the the deviations from the centroids.
- External Evaluation: Minimizing the deviations from some known "labels"
- Manual Evaluation: A human expert decides whether or not it's good
- Indirect Evaluation: Evaluating the utility of clustering in its intended application.

## Some Problems With These Evaluations

Internal evaluation measures suffer form the problem that they represent functions that are objectives for many clustering algorithms. So of course the result of the clustering algorithm will be such that the objective would be minimized.

External evaluation suffers from the fact that if we had labels to begin with then we wouldn't need to cluster. Practical applications of clustering occur usually when we don't have labels. On the other hand, possible labeling can reflect one possible partitioning of the data set. There could exist different, perhaps even better clustering.

## Internal Evaluation

We like to see a few qualities in cluster models

- *Robustness*: Refers to the effects of errors in data or missing observations, and changes in the data and methods.
- *Cohesiveness*: Clusters should be compact or high high intra-cluster similarity.
- Clusters should be dissimilar to separate clusters. Should have low inter-cluster similarity
- *Influence*: We should pay attention to and try to control for the influence of certain observations on the overall cluster

Let us focus on the second and third bullet point for now. Internal evaluation measures are best suited to get some insight into situations where one algorithm performs better than another, this does not imply that one algorithm produces more valid results than another.

### Davies-Bouldin Index

$$
DB = \frac{1}{n}\sum_{i=1}^n{max_{j\ne i}{(\frac{\sigma_i + \sigma_j}{d(c_i,c_j)})}}
$$

Where $n$ is the number of clusters, $c$ indicates a centroid, and $\sigma$ represents the deviation from the centroid.

Better clustering algorithms are indicated by smaller DB values.

### Dunn Index

$$
D= \frac{min_{1\le i < j \le n}{d(i,j)}}{max_{1\le k \le n}{d^\prime(k)}}
$$

The Dunn index aims to identify dense and well-separated clusters. This is defined as the ratio between the minimal inter-cluster distance to maximal intra-cluster distance.

High Dunn Index values are more desirable.

###Bootstrapping

In terms of robustness we can measure uncertainty in each of the individual clusters. This can be examined using a bootstrapping approach by Suzuki and Shimodaira (2006). The probability or "p-value" is the proportion of bootstrapped samples that contain the cluster. Larger p-values in this case indicate more support for the cluster.

This is available in R via `Pvclust`

### Split-Sample Validation

One approach to assess the effects of perturbations of the data is by randomly dividing the data into two subsets and performing an analysis on each subset separately. This method was proposed by McIntyre and Blashfield in 1980; their method involves the following steps

- Divide the sample in two and perform a cluster analysis on one of the samples
  - Have a fixed rule for the number of clusters
- Determine the centroids of the clusters, and compute proximities between the objects in teh second sample and the centroids, classifying the objects into their nearest cluster.
- Cluster the second sample using the same methods as before and compare these two alternate clusterings using something like the *adjusted Rand index*.

![Adjusted Index](https://wikimedia.org/api/rest_v1/media/math/render/svg/b1850490e5209123ab6e5b905495b4d5f9a1f661)

## Influence of Individual Points

Using internal evaluation metrics, you can see the impact of each point by doing a "leave one out" analysis. Here you evaluate the dataset minus one point for each of the points.  If a positive difference is found, the point is regarded as a *facilitator*, whereas if it is negative then it is considered an *inhibitor*. once an influential inhibitor is found, the suggestion is to normally omit it from the clustering.

## R Package

`clValid` contains a variety of internal validation measures.

Paper: https://cran.r-project.org/web/packages/clValid/vignettes/clValid.pdf