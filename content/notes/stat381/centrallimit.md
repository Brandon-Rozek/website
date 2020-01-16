# Central Limit Theorem Lab

**Brandon Rozek**

## Introduction

The Central Limit Theorem tells us that if the sample size is large, then the distribution of sample means approach the Normal Distribution. For distributions that are more skewed, a larger sample size is needed, since that lowers the impact of extreme values on the sample mean.

### Skewness

Skewness can be determined by the following formula
$$
Sk = E((\frac{X - \mu}{\sigma})^3) = \frac{E((X - \mu)^3)}{\sigma^3}
$$
Uniform distributions have a skewness of zero. Poisson distributions however have a skewness of $\lambda^{-\frac{1}{2}}$. 

In this lab, we are interested in the sample size needed to obtain a distribution of sample means that is approximately normal.

### Shapiro-Wilk Test

In this lab, we will test for normality using the Shapiro-Wilk test. The null hypothesis of this test is that the data is normally distributed. The alternative hypothesis is that the data is not normally distributed. This test is known to favor the alternative hypothesis for a large number of sample means.  To circumvent this, we will test normality starting with a small sample size $n$ and steadily increase it until we obtain a distribution of sample means that has a p-value greater than 0.05 in the Shapiro-Wilk test.

This tells us that with a false positive rate of 5%, there is no evidence to suggest that the distribution of sample means don't follow the normal distribution.

We will use this test to look at the distribution of sample means of both the Uniform and Poisson distribution in this lab.

### Properties of the distribution of sample means

The Uniform distribution has a mean of $0.5$ and a standard deviation of $\frac{1}{\sqrt{12n}}$ and the Poisson distribution has a mean of $\lambda$ and a standard deviation of $\sqrt{\frac{\lambda}{n}}$.

## Methods

For the first part of the lab, we will sample means from a Uniform distribution and a Poisson distribution of $\lambda = 1$ both with a sample size $n = 5$.

Doing so shows us how the Uniform distribution is roughly symmetric while the Poisson distribution is highly skewed. This begs the question: what sample size $(n)$ do I need for the Poisson distribution to be approximately normal?

### Sampling the means

The maximum number of mean observations that the Shapiro-Wilk test allows is 5000 observations. Therefore, we will obtain `n` observations separately from both  the Uniform or Poisson distribution and calculate the mean from it. Repeating that process 5000 times.

The mean can be calculated from the following way
$$
Mean = \frac{\sum x_i}{n}
$$
Where $x_i$ is the observation obtained from the Uniform or Poisson distribution

### Iterating with the Shapiro-Wilk Test

Having a sample size of a certain amount doesn't always guarantee that it will fail to reject the Shapiro-Wilk test. Therefore, it is useful to run the test multiple times so that we can create a 95th percentile of sample sizes that fails to reject the Shapiro-Wilk test.

The issue with this is that lower lambda values result in higher skewness's. Which is described by the skewness formula. If a distribution has a high degree of skewness, then it will take a larger sample size n to make the sample mean distribution approximately normal.

Finding large values of n result in longer computational time. Therefore, the code takes this into account by starting at a larger value of n and/or incrementing by a larger value of n each iteration. Incrementing by a larger value of n decreases the precision, though that is the compromise I'm willing to take in order to achieve faster results.

Finding just the first value of $n$ that generates the sample means that fails to reject the Shapiro-Wilk test doesn't tell us much in terms of the sample size needed for the distribution of sample means to be approximately normal. Instead, it is better to run this process many times, finding the values of n that satisfy this condition multiple times. That way we can look at the distribution of sample sizes required and return back the 95th percentile.

Returning the 95th percentile tells us that 95% of the time, it was the sample size returned or lower that first failed to reject the Shapiro-Wilk test. One must be careful, because it can be wrongly interpreted as the sample size needed to fail to reject the Shapiro-Wilk test 95% of the time. Using that logic requires additional mathematics outside the scope of this paper. Returning the 95th percentile of the first sample size that failed to reject the Shapiro-Wilk test, however, will give us a good enough estimate for a sample size needed.

### Plots

Once a value for `n ` is determined, we sample the means of the particular distribution (Uniform/Poisson) and create histograms and Q-Q plots for each of the parameters we're interested in. We're looking to verify that the histogram looks symmetric and that the points on the Q-Q Plot fit closely to the Q-Q Line with one end of the scattering of points on the opposite side of the line as the other.



## Results

### Part I

Sampling the mean of the uniform distribution with $n = 5$ results in a mean of $\bar{x} = 0.498$ and standard deviation of $sd = 0.1288$. The histogram and Q-Q Plot can be seen in Figure I and Figure II respectively. 

$\bar{x}$ isn't far from the theoretical 0.5 and the standard deviation is also close to
$$
\frac{1}{\sqrt{12(5)}} \approx 0.129
$$
Looking at the histogram and Q-Q plot, it suggests that data is approximately normal. Therefore we can conclude that a sample size of 5 is sufficient for the sample mean distribution coming from the normal distribution to be approximately normal.

Sampling the mean of the Poisson distribution with $n = 5$ and $\lambda = 1$ results in a mean of $\bar{x} = 0.9918$ and a standard deviation of $sd = 0.443$. The histogram and Q-Q Plot can be seen in Figures III and IV respectively.

$\bar{x}$ is not too far from the theoretical $\lambda = 1$, the standard deviation is a bit farther from the theoretical
$$
\sqrt{\frac{\lambda}{n}} = \sqrt{\frac{1}{5}} = 0.447
$$
Looking at the Figures, however, shows us that the data does not appear normal. Therefore, we cannot conclude that 5 is a big enough sample size for the Poisson Distribution of $\lambda = 1$ to be approximately normal.

### Part II

Running the algorithm I described, I produced the following table

| $\lambda$ | Skewness | Sample Size Needed | Shapiro-Wilk P-Value | Average of Sample Means | Standard Deviation of Sample Means | Theoretical Standard Deviation of Sample Means |
| --------- | -------- | ------------------ | -------------------- | ----------------------- | ---------------------------------- | ---------------------------------------- |
| 0.1       | 3.16228  | 2710               | 0.05778              | 0.099                   | 0.0060                             | 0.0061                                   |
| 0.5       | 1.41421  | 802                | 0.16840              | 0.499                   | 0.0250                             | 0.0249                                   |
| 1         | 1.00000  | 215                | 0.06479              | 1.000                   | 0.0675                             | 0.0682                                   |
| 5         | 0.44721  | 53                 | 0.12550              | 4.997                   | 0.3060                             | 0.3071                                   |
| 10        | 0.31622  | 31                 | 0.14120              | 9.999                   | 0.5617                             | 0.5679                                   |
| 50        | 0.14142  | 10                 | 0.48440              | 50.03                   | 2.2461                             | 2.2361                                   |
| 100       | 0.10000  | 6                  | 0.47230              | 100.0027                | 4.1245                             | 4.0824                                   |

The skewness was derived from the formula in the first section while the sample size was obtained by looking at the .95 blue quantile line in Figures XVIII-XIV. The rest of the columns are obtained from the output of the R Code function `show_results`.

Looking at the histograms and Q-Q Plots produced by the algorithm, the distribution of sample means distributions are all roughly symmetric. The sample means are also tightly clustered around the Q-Q line, showing that the normal distribution is a good fit. This allows us to be confident that using these values of `n` as the sample size would result in the distribution of sample means of Uniform or Poisson (with a given lambda) to be approximately normal.

All the values of the average sampling means are within 0.001 of the theoretical average of sample means. The standard deviation of sample means slightly increase as the value of $\lambda$ increases, but it still is quite low.

## Conclusion

The table in the results section clearly show that as the skewness increases, so does the sample size needed to make the distribution of sample means approximately normal. This shows the central limit theorem in action in that no matter the skewness, if you obtain a large enough sample, the distribution of sample means will be approximately normal.

These conclusions pave the way for more interesting applications such as hypothesis testing and confidence intervals.

## Appendix

### Figures

#### Figure I, Histogram of Sample Means coming from a Uniform Distribution with sample size of 5

![part1histunif](/home/rozek/Pictures/stat381lab3/part1histunif.png)

#### Figure II, Q-Q Plot of Sample Means coming from a Uniform Distribution with sample size of 5

![part1qunif](/home/rozek/Pictures/stat381lab3/part1qunif.png)

#### Figure III, Histogram of Sample Means coming from a Poisson Distribution with $\lambda = 1$ and sample size of 5

![part1histpoisson](/home/rozek/Pictures/stat381lab3/part1histpoisson.png)

#### Figure IV, Q-Q Plot of Sample Means coming from Poisson Distribution with $\lambda = 1$ and sample size of 5 

![part1qpoisson](/home/rozek/Pictures/stat381lab3/part1qpoisson.png)

#### Figure V, Histogram of Sample Means coming from Poisson Distribution with $\lambda = 0.1$ and sample size of 2710

![histpoisson01](/home/rozek/Pictures/stat381lab3/histpoisson01.png)

#### Figure VI, Q-Q Plot of Sample Means coming from Poisson Distribution with $\lambda = 0.1$ and sample size of 2710

![qpoisson01](/home/rozek/Pictures/stat381lab3/qpoisson01.png)

#### Figure VII, Histogram of Sample Means coming from Poisson Distribution with $\lambda = 0.5$ and sample size of 516

![histpoisson05](/home/rozek/Pictures/stat381lab3/histpoisson05.png)

#### Figure VII, Q-Q Plot of Sample Means coming from Poisson Distribution with $\lambda = 0.5$ and sample size of 516

![qpoisson05](/home/rozek/Pictures/stat381lab3/qpoisson05.png)

#### Figure VIII, Histogram of Sample Means coming from Poisson Distribution with $\lambda = 1$ and sample size of 215

![histpoisson1](/home/rozek/Pictures/stat381lab3/histpoisson1.png)

#### Figure IX, Q-Q Plot of Sample Means coming from Poisson Distribution with $\lambda = 1$ and sample size of 215

![qpoisson1](/home/rozek/Pictures/stat381lab3/qpoisson1.png)

#### Figure X, Histogram of Sample Means coming from Poisson Distribution of $\lambda = 5$ and sample size of 53

![histpoisson5](/home/rozek/Pictures/stat381lab3/histpoisson5.png)

#### Figure XI, Q-Q Plot of Sample Means coming from Poisson Distribution of $\lambda = 5$ and sample size of 53

![qpoisson5](/home/rozek/Pictures/stat381lab3/qpoisson5.png)

#### Figure XII, Histogram of Sample Means coming from Poisson Distribution of $\lambda = 10$ and sample size of 31

![histpoisson10](/home/rozek/Pictures/stat381lab3/histpoisson10.png)

#### Figure XIII, Q-Q Plot of Sample Means coming from Poisson Distribution of $\lambda = 10$ and sample size of 31

![qpoisson10](/home/rozek/Pictures/stat381lab3/qpoisson10.png)

#### Figure XIV, Histogram of Sample Means coming from Poisson Distribution of $\lambda = 50$ and sample size of 10

![histpoisson50](/home/rozek/Pictures/stat381lab3/histpoisson50.png)

#### Figure XV, Q-Q Plot of Sample Means coming from Poisson Distribution of $\lambda = 50$ and sample size of 10

![qpoisson50](/home/rozek/Pictures/stat381lab3/qpoisson50.png)

#### Figure XVI, Histogram of Sample Means coming from Poisson Distribution of $\lambda = 100$ and sample size of 6

![histpoisson100](/home/rozek/Pictures/stat381lab3/histpoisson100.png)

#### Figure XVII, Q-Q Plot of Sample Means coming from Poisson Distribution of $\lambda = 100$ and sample size of 6

![qpoisson100](/home/rozek/Pictures/stat381lab3/qpoisson100.png)

#### Figure XVIII, Histogram of sample size needed to fail to reject the normality test for Poisson Distribution of $\lambda = 0.1$ 

![histl01](/home/rozek/Pictures/stat381lab3/histl01.png)

#### Figure XIX, Histogram of sample size needed to fail to reject the normality test for Poisson Distribution of $\lambda = 0.5$

![histl05](/home/rozek/Pictures/stat381lab3/histl05.png)

#### Figure XX, Histogram of sample size needed to fail to reject the normality test for Poisson Distribution of $\lambda = 1$

![histl1.0](/home/rozek/Pictures/stat381lab3/histl1.0.png)

#### Figure XXI, Histogram of sample size needed to fail to reject the normality test for Poisson Distribution of $\lambda = 5$

![histl5](/home/rozek/Pictures/stat381lab3/histl5.png)

####Figure XXII, Histogram of sample size needed to fail to reject the normality test for Poisson Distribution of $\lambda = 10$

![histl10](/home/rozek/Pictures/stat381lab3/histl10.png)

####Figure XXIII, Histogram of sample size needed to fail to reject the normality test for Poisson Distribution of $\lambda = 50$

![histl50](/home/rozek/Pictures/stat381lab3/histl50.png)

#### Figure XXIV, Histogram of sample size needed to fail to reject the normality test for Poisson Distribution of $\lambda = 100$

![histl100](/home/rozek/Pictures/stat381lab3/histl100.png)

### R Code

```R
rm(list=ls())
library(ggplot2)

sample_mean_uniform = function(n) {
  xbarsunif = numeric(5000)
  for (i in 1:5000) {
    sumunif = 0
    for (j in 1:n) {
      sumunif = sumunif + runif(1, 0, 1)
    }
    xbarsunif[i] = sumunif / n 
  }
  xbarsunif
}

sample_mean_poisson = function(n, lambda) {
  xbarspois = numeric(5000)
  for (i in 1:5000) {
    sumpois = 0
    for (j in 1:n) {
      sumpois = sumpois + rpois(1, lambda) 
    }
    xbarspois[i] = sumpois / n
  }
  xbarspois
}


poisson_n_to_approx_normal = function(lambda) {
  print(paste("Looking at Lambda =", lambda))
  ns = c()
  
  # Speed up computation of lower lambda values by starting at a different sample size
  # and/or lowering the precision by increasing the delta sample size
  # and/or lowering the number of sample sizes we obtain from the shapiro loop
  increaseBy = 1;
  iter = 3;
  startingValue = 2
  if (lambda == 0.1) {
    startingValue = 2000;
    iter = 3;
    increaseBy = 50;
  } else if (lambda == 0.5) {
    startingValue = 200;
    iter = 5;
    increaseBy = 10;
  } else if (lambda == 1) {
    startingValue = 150;
    iter = 25;
  } else if (lambda == 5) {
    startingValue = 20;
    iter = 50;
    startingValue = 10;
  } else if (lambda == 10) {
    iter = 100;
  } else {
    iter = 500;
  }
  
  progressIter = 1
  for (i in 1:iter) {
    
    # Include a progress indicator for personal sanity
    if (i / iter > .1 * progressIter) {
      print(paste("Progress", i / iter * 100, "% complete"))
      progressIter = progressIter + 1
    }
    
    n = startingValue

    dist = sample_mean_poisson(n, lambda)
    p.value = shapiro.test(dist)$p.value
    while (p.value < 0.05) {
      n = n + increaseBy
      dist = sample_mean_poisson(n, lambda)
      p.value = shapiro.test(dist)$p.value
      
      # More sanity checks
      if (n %% 10 == 0) {
        print(paste("N =", n, " p.value =", p.value))
      }
    }
    ns = c(ns, n)
  }

  print(ggplot(data.frame(ns), aes(x = ns)) +
          geom_histogram(fill = 'white', color = 'black', bins = 10) +
          geom_vline(xintercept = ceiling(quantile(ns, .95)), col = '#0000AA') +
          ggtitle(paste("Histogram of N needed for Poisson distribution of lambda =", lambda)) +
          xlab("N") +
          ylab("Count") +
          theme_bw())
  
  
  ceiling(quantile(ns, .95)) #95% of the time, this value of n will give you a sampling distribution that is approximately normal
}

uniform_n_to_approx_normal = function() {
  ns = c()
  progressIter = 1
  
  for (i in 1:500) {
    
    # Include a progress indicator for personal sanity
    if (i / 500 > .1 * progressIter) {
      print(paste("Progress", i / 5, "% complete"))
      progressIter = progressIter + 1
    }
    
    n = 2
    dist = sample_mean_uniform(n)
    p.value = shapiro.test(dist)$p.value
    while (p.value < 0.05) {
      n = n + 1
      dist = sample_mean_uniform(n)
      p.value = shapiro.test(dist)$p.value
      
      if (n %% 10 == 0) {
        print(paste("N =", n, " p.value =", p.value))
      }
      
    }
    
    ns = c(ns, n)
  }
  
  print(ggplot(data.frame(ns), aes(x = ns)) +
    geom_histogram(fill = 'white', color = 'black', bins = 10) +
    geom_vline(xintercept = ceiling(quantile(ns, .95)), col = '#0000AA') +
    ggtitle("Histogram of N needed for Uniform Distribution") +
    xlab("N") +
    ylab("Count") +
    theme_bw())
  
  ceiling(quantile(ns, .95)) #95% of the time, this value of n will give you a sampling distribution that is approximately normal
}



show_results = function(dist) {
  print(paste("The mean of the sample mean distribution is:", mean(dist)))
  print(paste("The standard deviation of the sample mean distribution is:", sd(dist)))
  print(shapiro.test(dist))
  print(ggplot(data.frame(dist), aes(x = dist)) +
          geom_histogram(fill = 'white', color = 'black', bins = 20) +
          ggtitle("Histogram of Sample Means") +
          xlab("Mean") + 
          ylab("Count") +
          theme_bw())
  qqnorm(dist, pch = 1, col = '#001155', main = "QQ Plot", xlab = "Sample Data", ylab = "Theoretical Data")
  qqline(dist, col="#AA0000", lty=2)
}


## PART I
uniform_mean_dist = sample_mean_uniform(n = 5)
poisson_mean_dist = sample_mean_poisson(n = 5, lambda = 1)

show_results(uniform_mean_dist)
show_results(poisson_mean_dist)

## PART II

print("Starting Algorithm to Find Sample Size Needed for the Poisson Distribution of Lambda = 0.1");
n.01 = poisson_n_to_approx_normal(0.1)
show_results(sample_mean_poisson(n.01, 0.1))
print("Starting Algorithm to Find Sample Size Needed for the Poisson Distribution of Lambda = 0.5");
n.05 = poisson_n_to_approx_normal(0.5)
show_results(sample_mean_poisson(n.05, 0.5))
print("Starting Algorithm to Find Sample Size Needed for the Poisson Distribution of Lambda = 1");
n.1  = poisson_n_to_approx_normal(1)
show_results(sample_mean_poisson(n.1, 1))
print("Starting Algorithm to Find Sample Size Needed for the Poisson Distribution of Lambda = 5");
n.5  = poisson_n_to_approx_normal(5)
show_results(sample_mean_poisson(n.5, 5))
print("Starting Algorithm to Find Sample Size Needed for the Poisson Distribution of Lambda = 10");
n.10 = poisson_n_to_approx_normal(10)
show_results(sample_mean_poisson(n.10, 10))
print("Starting Algorithm to Find Sample Size Needed for the Poisson Distribution of Lambda = 50");
n.50 = poisson_n_to_approx_normal(50)
show_results(sample_mean_poisson(n.50, 50))
print("Starting Algorithm to Find Sample Size Needed for the Poisson Distribution of Lambda = 100");
n.100 = poisson_n_to_approx_normal(100)
show_results(sample_mean_poisson(n.100, 100))

print("Starting Algorithm to Find Sample Size Needed for the Uniform Distribution")
n.uniform = uniform_n_to_approx_normal()
show_results(sample_mean_uniform(n.uniform))
```

