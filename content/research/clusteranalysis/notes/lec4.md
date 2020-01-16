# Principal Component Analysis Part 2: Formal Theory

##Properties of PCA

There are a number of ways to maximize the variance of a principal component. To create an unique solution we should impose a constraint. Let us say that the sum of the square of the coefficients must equal 1. In vector notation this is the same as
$$
a_i^Ta_i = 1
$$
Every future principal component is said to be orthogonal to all the principal components previous to it. 
$$
a_j^Ta_i = 0, i < j
$$
The total variance of the $q$ principal components will equal the total variance of the original variables
$$
\sum_{i = 1}^q {\lambda_i} = trace(S)
$$
Where $S$ is the sample covariance matrix.

The proportion of accounted variation in each principle component is
$$
P_j = \frac{\lambda_j}{trace(S)}
$$
From this, we can generalize to the first $m$ principal components where $m < q$ and find the proportion $P^{(m)}$ of variation accounted for
$$
P^{(m)} = \frac{\sum_{i = 1}^m{\lambda_i}}{trace(S)}
$$
You can think of the first principal component as the line of best fit that minimizes the residuals orthogonal to it.

### What to watch out for

As a reminder to the last lecture, *PCA is not scale-invariant*. Therefore, transformations done to the dataset before PCA and after PCA often lead to different results and possibly conclusions.

Additionally, if there are large differences between the variances of the original variables, then those whose variances are largest will tend to dominate the early components.

Therefore, principal components should only be extracted from the sample covariance matrix when all of the original variables have roughly the **same scale**.

### Alternatives to using the Covariance Matrix

But it is rare in practice to have a scenario when all of the variables are of the same scale. Therefore, principal components are typically extracted from the **correlation matrix** $R$

Choosing to work with the correlation matrix rather than the covariance matrix treats the variables as all equally important when performing PCA.

##  Example Derivation: Bivariate Data

Let $R$ be the correlation matrix
$$
R = \begin{pmatrix}
1 & r \\
r & 1
\end{pmatrix}
$$
Let us find the eigenvectors and eigenvalues of the correlation matrix
$$
det(R - \lambda I) = 0
$$

$$
(1-\lambda)^2 - r^2 = 0
$$

$$
\lambda_1 = 1 + r, \lambda_2 = 1 - r
$$

Let us remember to check the condition "sum of the principal components equals the trace of the correlation matrix":
$$
\lambda_1 + \lambda_2 = 1+r + (1 - r) = 2 = trace(R)
$$

###Finding the First Eigenvector

Looking back at the characteristic equation
$$
Ra_1 = \lambda a_1
$$
We can get the following two formulas
$$
a_{11} + ra_{12} = (1+r)a_{11} \tag{1}
$$

$$
ra_{11} + a_{12} = (1 + r)a_{12} \tag{2}
$$

Now let us find out what $a_{11}$ and $a_{12}$ equal. First let us solve for $a_{11}$ using equation $(1)$
$$
ra_{12} = (1+r)a_{11} - a_{11}
$$

$$
ra_{12} = a_{11}(1 + r - 1)
$$

$$
ra_{12} = ra_{11}
$$

$$
a_{12} = a_{11}
$$

Where $r$ does not equal $0$.

Now we must apply the condition of sum squares
$$
a_1^Ta_1 = 1
$$

$$
a_{11}^2 + a_{12}^2  = 1
$$

Recall that $a_{12} = a_{11}$ 
$$
2a_{11}^2 = 1
$$

$$
a_{11}^2 = \frac{1}{2}
$$

$$
a_{11} =\pm \frac{1}{\sqrt{2}}
$$

For sake of choosing a value, let us take the principal root and say $a_{11} = \frac{1}{\sqrt{2}}$

###Finding the Second Eigenvector

Recall the fact that each subsequent eigenvector is orthogonal to the first. This means
$$
a_{11}a_{21} + a_{12}a_{22} = 0
$$
Substituting the values for $a_{11}$ and $a_{12}$ calculated in the previous section
$$
\frac{1}{\sqrt{2}}a_{21} + \frac{1}{\sqrt{2}}a_{22} = 0
$$

$$
a_{21} + a_{22} = 0
$$

$$
a_{21} = -a_{22}
$$

Since this eigenvector also needs to satisfy the first condition, we get the following values
$$
a_{21} = \frac{1}{\sqrt{2}} , a_{22} = \frac{-1}{\sqrt{2}}
$$

### Conclusion of Example

From this, we can say that the first principal components are given by
$$
y_1 = \frac{1}{\sqrt{2}}(x_1 + x_2), y_2 = \frac{1}{\sqrt{2}}(x_1-x_2)
$$
With the variance of the first principal component being given by $(1+r)$ and the second by $(1-r)$

Due to this, as $r$ increases, so does the variance explained in the first principal component. This in turn, lowers the variance explained in the second principal component.

## Choosing a Number of Principal Components

Principal Component Analysis is typically used in dimensionality reduction efforts. Therefore, there are several strategies for picking the right number of principal components to keep. Here are a few:

- Retain enough principal components to account for 70%-90% of the variation
- Exclude principal components where eigenvalues are less than the average eigenvalue
- Exclude principal components where eigenvalues are less than one.
- Generate a Scree Plot
  - Stop when the plot goes from "steep" to "shallow"
  - Stop when it essentially becomes a straight line.