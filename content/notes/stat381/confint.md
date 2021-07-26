---
title: Confidence Interval
showthedate: false
---

## Introduction

Confidence intervals expands the concept of a point estimation by giving a margin of error such that one can be confident that a certain percentage of the time the true parameter falls within that interval.

In this lab, we will look at confidence intervals for a mean. This lab focuses on a certain method of confidence intervals that depends on the distribution of sample means being Normal. We will show how the violation of this assumption impacts the probability that the true parameter falls within the interval.

## Methods

The observed level of confidence tells us the proportion of times the true mean falls within a confidence interval. To show how the violation of the Normality assumption affects this, we will sample from both a Normal distribution, T distribution, and exponential distribution with different sample sizes.

The normal and T distributions are sampled with a mean of 5 and a standard deviation of 2. The exponential deviation is sampled with a lambda of 2 or mean of 0.5.

From the samples, we obtain the mean and the upper/lower bounds of the confidence interval. This is performed 100,000 times. That way we obtain a distribution of these statistics.

We know that a confidence interval is valid, if the lower bound is no more than the true mean and the upper bound is no less than the true mean.  From this definition, we can compute a proportion of observed confidence from the simulations

### Visualizations

From the distributions of statistics, we can create visualizations to support the understanding of confidence intervals.

The first one is a scatterplot of lower bounds vs upper bounds. This plot demonstrates the valid confidence intervals in blue and the invalid ones in red. It demonstrates how confidence intervals that are invalid are not located inside the box.

The second visualization is a histogram of all the sample means collected. The sample means that didn't belong to a valid confidence interval are shaded in red. This graphic helps demonstrate the type I errors on both sides of the distribution. 

In this lab, we're interested in seeing how our observed level of confidence differs from our theoretical level of confidence (95%) when different sample sizes and distributions are applied.

## Results

We can see from the table section in the Appendix that sampling from a Normal or t distribution does not adversely affect our observed level of confidence. The observed level of confidence varies slightly from the theoretical level of confidence of 0.95.

When sampling from the exponential distribution, however, the observed level of confidence highly depends upon the sample size.

Looking at Table III, we can see that for a sample size of 10, the observed level of confidence is at a meager 90%. This is 5% off from our theoretical level of confidence.  This shows how the normality assumption is vital to the precision of our estimate. 

This comes from the fact that using this type of confidence interval on a mean from a  non-normal distribution requires a large sample size for the central limit theorem to take affect.

The central limit theorem states that if the sample size is "large", the distribution of sample means approach the normal distribution. You can see how in Figure XVIII, the distribution of sample means is skewed, though as the sample size increases, the distribution of sample means become more symmetric (Figure XIX).

## Conclusion

From this, we can conclude that violating the underlying assumption of normality decreases the observed level of confidence. We can mitigate the decrease of the observed level of confidence when sampling means from a non-normal distribution by having a larger sample size. This is due to the central limit theorem.

## Appendix

### Tables

#### Table I. Sampling from Normal

| Sample Size | Proportion of Means Within CI |
| ----------- | ----------------------------- |
| 10          | 0.94849                       |
| 20          | 0.94913                       |
| 50          | 0.95045                       |
| 100         | 0.94955                       |



#### Table II. Sampling from T Distribution

| Sample Size | Proportion of Means Within CI |
| ----------- | ----------------------------- |
| 10          | 0.94966                       |
| 20          | 0.94983                       |
| 50          | 0.94932                       |
| 100         | 0.94999                       |



#### Table III. Sampling from Exponential Distribution

| Sample Size | Proportion of Means Within CI |
| ----------- | ----------------------------- |
| 10          | 0.89934                       |
| 20          | 0.91829                       |
| 50          | 0.93505                       |
| 100         | 0.94172                       |





### Figures

#### Normal Distribution

##### Figure I. Scatterplot of Bounds for Normal Distribution of Sample Size 10

![normal10scatter](/home/rozek/Pictures/statlab4/normal10scatter.png)

##### Figure II. Histogram of Sample Means for Normal Distribution of Sample Size 10

![normal10hist](/home/rozek/Pictures/statlab4/normal10hist.png)

##### Figure III. Scatterplot of Bounds for Normal Distribution of Sample Size 20

![normal20scatterplot](/home/rozek/Pictures/statlab4/normal20scatterplot.png)

##### Figure IV. Histogram of Sample Means for Normal Distribution of Sample Size 20

![normal20hist](/home/rozek/Pictures/statlab4/normal20hist.png)

##### Figure VScatterplot of Bounds for Normal Distribution of Sample Size 50

![normal50scatterplot](/home/rozek/Pictures/statlab4/normal50scatterplot.png)

##### Figure VI. Histogram of Sample Means for Normal Distribution of Sample Size 50

![normal50hist](/home/rozek/Pictures/statlab4/normal50hist.png)

##### Figure VII. Scatterplot of Bounds for Normal Distribution of Sample Size 100

![normal100scatterplot](/home/rozek/Pictures/statlab4/normal100scatterplot.png)

##### Figure VIII. Histogram of Sample Means for Normal Distribution of Sample Size 100

![normal100hist](/home/rozek/Pictures/statlab4/normal100hist.png)

#### T Distribution

##### Figure IX. Scatterplot of Bounds for T Distribution of Sample Size 10

![t10scatterplot](/home/rozek/Pictures/statlab4/t10scatterplot.png)

##### Figure X. Histogram of Sample Means for T Distribution of Sample Size 10

![t10hist](/home/rozek/Pictures/statlab4/t10hist.png)

##### Figure XI. Scatterplot of Bounds for T Distribution of Sample Size 20

![t20scatterplot](/home/rozek/Pictures/statlab4/t20scatterplot.png)

##### Figure XII. Histogram of Sample Means for T Distribution of Sample Size 20

![t20hist](/home/rozek/Pictures/statlab4/t20hist.png)

##### Figure XIII. Scatterplot of Bounds for T Distribution of Sample Size 50

![t50scatter](/home/rozek/Pictures/statlab4/t50scatter.png)

##### Figure XIV. Histogram of Sample Means for T Distribution of Sample Size 50

![t50hist](/home/rozek/Pictures/statlab4/t50hist.png)

##### Figure XV. Scatterplot of Bounds for T Distribution of Sample Size 100

![t100scatter](/home/rozek/Pictures/statlab4/t100scatter.png)

##### Figure XVI. Histogram of Sample Means for T Distribution of Sample Size 100

![t100hist](/home/rozek/Pictures/statlab4/t100hist.png)

#### Exponential Distribution

##### Figure XVII. Scatterplot of Bounds for Exponential Distribution of Sample Size 10

![exp10scatter](/home/rozek/Pictures/statlab4/exp10scatter.png)

##### Figure XVIII. Histogram of Sample Means for Exponential Distribution of Sample Size 10

![exp10hist](/home/rozek/Pictures/statlab4/exp10hist.png)

##### Figure XIX. Scatterplot of Bounds for Exponential Distribution of Sample Size 20

![exp20scatter](/home/rozek/Pictures/statlab4/exp20scatter.png)

##### Figure XX. Histogram of Sample Means for Exponential Distribution of Sample Size 20

![exp20hist](/home/rozek/Pictures/statlab4/exp20hist.png)

##### Figure XXI. Scatterplot of Bounds for Exponential Distribution of Sample Size 50

![exp50scatter](/home/rozek/Pictures/statlab4/exp50scatter.png)

##### Figure XXII. Histogram of Sample Means for Exponential Distribution of Sample Size 50

![exp50hist](/home/rozek/Pictures/statlab4/exp50hist.png)

##### Figure XXIII. Scatterplot of Bounds for Exponential Distribution of Sample Size 100

![exp100scatter](/home/rozek/Pictures/statlab4/exp100scatter.png)

##### Figure XXIV. Histogram of Sample Means for Exponential Distribution of Sample Size 100

![exp100hist](/home/rozek/Pictures/statlab4/exp100hist.png)



### R Code

```R
rm(list=ls())
library(ggplot2)
library(functional) # For function currying

proportion_in_CI = function(n, mu, dist) {
  
  # Preallocate vectors
  lower_bound = numeric(100000)
  upper_bound = numeric(100000)
  means = numeric(100000)
  
  number_within_CI = 0
  
  ME = 1.96 * 2 / sqrt(n) ## Normal Margin of Error
  
  for (i in 1:100000) {
    x = numeric(n)
    
    # Sample from distribution
    if (dist == "Normal" | dist == "t") {
      x = rnorm(n,mu,2)
    } else if (dist == "Exponential") {
      x = rexp(n, 1 / mu)
    }
   
    ## Correct ME if non-normal
    if (dist != "Normal") {
      ME = qt(0.975,n-1)*sd(x)/sqrt(n)
    }
    
    ## Store statistics
    means[i] = mean(x)
    lower_bound[i] = mean(x) - ME
    upper_bound[i] = mean(x) + ME
    
    # Is Confidence Interval Valid?
    if (lower_bound[i] < mu & upper_bound[i] > mu) {
      number_within_CI = number_within_CI + 1 
    }
  }
  
  # Prepare for plotting
  lbub = data.frame(lower_bound, upper_bound, means)
  lbub$col = ifelse(lbub$lower_bound < mu & lbub$upper_bound > mu, 'Within CI', 'Outside CI')
  print(ggplot(lbub, aes(x = lower_bound, y = upper_bound, col = col)) +
          geom_point(pch = 1) +
          geom_hline(yintercept = mu, col = '#000055') +
          geom_vline(xintercept = mu, col = '#000055') +
          ggtitle(paste("Plot of Lower Bounds vs Upper Bounds with Sample Size of ", n)) +
          xlab("Lower Bound") +
          ylab("Upper Bounds") +
          theme_bw()
  )
  print(ggplot(lbub, aes(x = means, fill = col)) +
          geom_histogram(color = 'black') +
          ggtitle(paste("Histogram of Sample Means with Sample Size of ", n)) +
          xlab("Sample Mean") +
          ylab("Count") +
          theme_bw()
  )
  
  # Return proportion within CI
  number_within_CI / 100000
}

sample_sizes = c(10, 20, 50, 100)

### PART I
proportion_in_CI_Normal = Curry(proportion_in_CI, dist = "Normal", mu = 5)
p_norm = sapply(sample_sizes, proportion_in_CI_Normal)
sapply(p_norm, function(x) {
  cat("The observed proportion of intervals containing mu is", x, "\n")
  invisible(x)
})


### PART II
proportion_in_CI_T = Curry(proportion_in_CI, dist = "t", mu = 5)
p_t = sapply(sample_sizes, proportion_in_CI_T)
sapply(p_t, function(x) {
  cat("The observed proportion of intervals containing mu is", x, "\n")
  invisible(x)
})

### PART III
proportion_in_CI_Exp = Curry(proportion_in_CI, dist = "Exponential", mu = 0.5)
p_exp = sapply(sample_sizes, proportion_in_CI_Exp)
sapply(p_exp, function(x) {
  cat("The observed proportion of intervals containing mu is", x, "\n")
  invisible(x)
})
```

