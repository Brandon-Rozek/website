---
title: Feature Selection
---

Feature selection is the process of selecting a subset of relevant features for use in model construction. The core idea is that data can contain many features that are redundant or irrelevant. Therefore, removing it will not result in much loss of information. We also wish to remove features that do not help in our goal.

Feature selection techniques are usually applied in domains where there are many features and comparatively few samples.

## Techniques

The brute force feature selection method exists to exhaustively evaluate all possible combinations of the input features, and find the best subset. The computational cost of this approach is prohibitively high and includes a considerable risk of overfitting to the data. 

The techniques below describe greedy approaches to this problem. Greedy algorithms are ones that don't search the entire possible space but instead converges towards local maximums/minimums.

### Wrapper Methods

This uses a predictive model to score feature subsets. Each new subset is used to train a model, which is tested on a hold-out set. The error rate of the model results in a score for that subset. This method is computationally intensive, but usually provides the best performing feature set for that particular type of model.

### Filter Methods

This method uses a proxy measure instead of the error rate. The proxy measure can be specifically chosen to be faster to compute while still capturing the essence of the feature set. Common implementations include:

- Mutual information
- Pointwise mutual information
- Pearson product-moment correlation coefficient
- Relief-based algorithms
- Inter/intra class distances
- Scores of significance tests

Many filters provide a feature ranking rather than producing an explicit best feature subset

### Embedded Methods

This is a catch-all group of techniques which perform feature selection as part of the model. For example, the LASSO linear model penalizes the regression coefficients shrinking unimportant ones to zero.

Stepwise regression is a commonly used feature selection technique that acts greedily by adding the feature that results in the best result each turn.