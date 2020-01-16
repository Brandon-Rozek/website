# Optimality Criteria

Falling under wrapper methods, optimality criterion are often used to aid in model selection. These criteria provide a measure of fit for the data to a given hypothesis. 

## Akaike Information Criterion (AIC)

AIC is an estimator of <u>relative</u> quality of statistical models for a given set of data. Given a collection of models for the data, AIC estimates the quality  of each model relative to each other.

This way, AIC provides a means for model selection. AIC offers an estimate of the relative information lost when a given model is used. 

This metric does not say anything about the absolute quality of a model but only serves for comparison between models. Therefore, if all the candidate models fit poorly to the data, AIC will not provide any warnings.

It is desired to pick the model with the lowest AIC.

AIC is formally defined as
$$
AIC = 2k - 2\ln{(\hat{L})}
$$


## Bayesian Information Criterion (BIC)

This metric is based on the likelihood function and is closely related to the Akaike information criterion. It is desired to pick the model with the lowest BIC. 

BIC is formally defined as
$$
BIC = \ln{(n)}k - 2\ln{(\hat{L})}
$$

Where $\hat{L}$ is the maximized value of the likelihood function for the model $M$.
$$
\hat{L} = p(x | \hat{\theta}, M)
$$
$x$ is the observed data, $n$ is the number of observations, and $k$ is the number of parameters estimated.



### Properties of BIC

- It is independent from the prior
- It penalizes the complexity of the model in terms of the number of parameters

### Limitations of BIC

- Approximations are only valid for sample sizes much greater than the number of parameters (dense data)
- Cannot handle collections of models in high dimension

### Differences from AIC

AIC is mostly used when comparing models. BIC asks the question of whether or not the model resembles reality. Even though they have similar functions, they are separate goals.

## Mallow's $C_p$

$C_p$ is used to assess the fit of a regression model that has been estimated using ordinary least squares. A small value of $C_p$ indicates that the model is relatively precise.

The $C_p$ of a model is defined as
$$
C_p = \frac{\sum_{i =1}^N{(Y_i - Y_{pi})^2}}{S^2}- N + 2P
$$

- $Y_pi$ is the predicted value of the $i$th observation of $Y$ from the $P$ regressors

- $S^2$ is the residual mean square after regression on the complete set of regressors and can be estimated by mean square error $MSE$,

- $N$ is the sample size.

An alternative definition is


$$
C_p = \frac{1}{n}(RSS + 2d\hat{\sigma}^2)
$$

- $RSS$ is the residual sum of squares
- $d$ is the number of predictors
- $\hat{\sigma}^2$ refers to an estimate of the variances associated with each response in the linear model

## Deviance Information Criterion

The DIC is a hierarchical modeling generalization of the AIC and BIC. it is useful in Bayesian model selection problems where posterior distributions of the model was <u>obtained by a Markov Chain Monte Carlo simulation</u>.

This method is only valid if the posterior distribution is approximately multivariate normal.

Let us define the deviance as
$$
D(\theta) = -2\log{(p(y|\theta))} + C
$$
Where $y$ is the data and $\theta$ are the unknown parameters of the model.

Let us define a helper variable $p_D$ as the following
$$
p_D = \frac{1}{2}\hat{Var}(D(\theta))
$$
Finally the deviance information criterion can be calculated as
$$
DIC = D(\bar{\theta}) + 2p_D
$$
Where $\bar{theta}$ is the expectation of $\theta$.

