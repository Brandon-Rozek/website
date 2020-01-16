# Principal Component Analysis Pt. 1

## What is PCA?

Principal component analysis is a statistical procedure that performs an orthogonal transformation to convert a set of variables into a set of linearly uncorrelated variables called principle components.

Number of distinct principle components equals $min(\# Variables, \# Observations - 1)$

The transformation is defined in such a way that the first principle component has the largest possible variance explained in the data.

Each succeeding component has the highest possible variance under the constraint of having to be orthogonal to the preceding components.

PCA is sensitive to the relative scaling of the original variables.

### Results of a PCA

Results are discussed in terms of *component scores* which is the transformed variables and *loadings* which is the weight by which each original variable should be multiplied to get the component score.

## Assumptions of PCA

1. Linearity
2. Large variances are important and small variances denote noise
3. Principal components are orthogonal

## Why perform PCA?

- Distance measures perform poorly in high-dimensional space (https://stats.stackexchange.com/questions/256172/why-always-doing-dimensionality-reduction-before-clustering)
- Helps eliminates noise from the dataset (https://www.quora.com/Does-it-make-sense-to-perform-principal-components-analysis-before-clustering-if-the-original-data-has-too-many-dimensions-Is-it-theoretically-unsound-to-try-to-cluster-data-with-no-correlation)
- One initial cost to help reduce further computations

## Computing PCA

1. Subtract off the mean of each measurement type
2. Compute the covariance matrix
3. Take the eigenvalues/vectors of the covariance matrix

## R Code

```R
pcal = function(data) {
  centered_data = scale(data)
  covariance = cov(centered_data)
  eigen_stuff = eigen(covariance)
  sorted_indices = sort(eigen_stuff$values, 
                        index.return = T, 
                        decreasing = T)$ix
  loadings = eigen_stuff$values[sorted_indices]
  components = eigen_stuff$vectors[sorted_indices,]
  combined_list = list(loadings, components)
  names(combined_list) = c("Loadings", "Components")
  return(combined_list)
}
```