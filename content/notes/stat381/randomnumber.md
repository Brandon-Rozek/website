---
title: Random Number Generation
showthedate: false
math: true
---

## Introduction

The generation of random numbers have a variety of applications including but not limited to the modeling of stochastic processes. It is important, therefore, to be able to generate any random number following a given distribution. One of the many ways to achieve this is to transform numbers sampled from a random uniform distribution. 

In this lab, we will  compare the effectiveness between the linear congruence method (LCM), `runif`, and `rexp` to generate random numbers. The programming language R will be used and different plots and summary statistics are drawn upon to analyze the effectiveness of the methods.

## Methods

### The Linear Congruential Method

The linear congruential method (LCM) is an algorithm that produces a sequence of pseudo-random numbers using the following recursive function
$$
X_{n + 1} = (aX_n + c)  \mod m
$$
The R code we use has a `c` value of 0 which is a special case known as the multiplicative congruential generator (MCG).

There are several conditions for using a MCG. First, the seed value must be co-prime to `m`. In other words, the greatest common denominator between the two must be 1. A function was written in R to check this. Secondly, `m` must be a prime number or a power of a prime number. 

#### Periodicity

An element of periodicity comes into play when dealing with pseudo-random number generators. Once the generator has produced a certain number of terms, it is shown to loop back to the first term of the sequence. It is advantageous, therefore, to keep the period high. 

The period in a MCG is at most `m - 1`. In this lab, `m` has a value of $2^{31}$ and only 100 numbers were sampled from the LCM. This allows us to avoid the issue of periodicity entirely in our analysis.

### Mersenne-Twister Method

The default pseudo-random number generator (pseudo RNG) in R is the Mersenne-Twister with the default seed value of the current time and the process id of the current R instance. Mersenne-Twister is part of a class of pseudo RNG called the generalized feedback register.  This class of pseudo RNGs provide a very long period (VLP) or in other words, a long cycle before the values start repeating. VLPs are often useful when executing large simulations in R.

Since this method is already coded in the `base` R-package, we will leave the implementation for the curious to research.

### The Uniform Distribution

#### Probability Mass Function

The uniform distribution function $Unif(\theta_1, \theta_2)$  has a probability mass function (PMF) of the following.
$$
f(x) = \frac{1}{\theta_2 - \theta_1}
$$
Where x is valid between [$\theta_1$, $\theta_2$].

In our case, we are producing numbers from [0,1]. We can therefore reduce the probability mass function to the following
$$
f(x) = 1
$$
#### Expected Value

The expected value can be defined as
$$
E(X) = \int_a^b xf(x)dx
$$
For the uniform distribution we're using that becomes
$$
E(X) = \int_0^1 xdx = \frac{1}{2}[x^2]_0^1 = \frac{1}{2}
$$
We should, therefore, expect the mean of the generated random number sequence to roughly equal $\frac{1}{2}$. 

#### Median

To find the median of the distribution, we need to find the point at which the cumulative density function (CDF) is equal to .5.
$$
\int_0^{Median(X)} f(x)dx = \frac{1}{2}
$$
$$
\int_0^{Median(X)} dx = \frac{1}{2}
$$

$$
[X]_0^{Median(X)} = \frac{1}{2}
$$

$$
Median(X) = \frac{1}{2}
$$

This shows us that the median of the distribution should be roughly equal to $\frac{1}{2}$ as well.

#### Analysis of Uniform Distribution Fit

The histogram of a uniform distribution of data should look rectangular in shape. This means that the counts of all the sub-intervals should be about the same.

Another way to test whether or not the distribution is a good fit is to use what is called a Quantile-Quantile plot (Q-Q Plot). This is a probability plot that compares the quantiles from the theoretical distribution, this is the uniform distribution, to that of the sample.

For a precise Q-Q Plot, we need a lot of quantiles to compare. In this lab, we will compare 100 different quantiles. The quantiles from the theoretical distribution can be easily derived from the fact that all value ranges are equally probable. The theoretical quantiles in this case is 0.01, 0.02, ..., 0.98, 0.99, 1. The sample quantiles are obtianed by receiving 100 observations from `runif` or the LCM. 

In the Q-Q plot, a good fit is shown when the points hug closely to the Q-Q line. It is also important to have symmetry in the points. This means that the points are ending on opposite sides of the Q-Q line.

For sake of exploration, we will use 5 different seed values for the linear congruential method (while making sure that the seed values are co-prime). We will then use the results of these and compare LCM to how the standard `runif` method generates random numbers.

### Exponential Distribution

#### Probability Mass Function and the Cumulative Density Function

The exponential distribution is a type of continuous distribution that is defined by the following PMF
$$
f(x) = \lambda e^{-\lambda t}
$$
We can find the CDF by taking the integral of the PMF.
$$
F(x) = \int f(x)dx = \lambda \int e^{-\lambda x} dx = \lambda * (\frac{-1}{\lambda}) e^{-\lambda x} + C = -e^{-\lambda x} + C
$$
One of the conditions for the cumulative density function is that as $x \to \infty$, $F(x) \to 1$.
$$
1 = \lim_{x \to \infty} (-e^{-\lambda x} + C) = \lim_{x \to \infty} (-e^{-\lambda x}) + lim_{x \to \infty} ( C) = \lim_{x \to \infty}(-e^{\lambda x}) + C
$$
This shows that $C = 1$, since $lim_{x \to \infty} (-e^{-\lambda x})$ is equal to 0. 

Substituting $C​$ gives us the following.
$$
F(x) = 1 - e^{-\lambda x}
$$

#### Expected Value

We can find the expected value using the formula described in the previous Expected Value section. Reflected in the bounds of integration is the domain of the exponential distribution $[0, \infty)$.
$$
E(X) = \lim_{a \to \infty}\int_0^a x \lambda e^{-\lambda x} dx
$$
The integral above features a product of two functions. So as an aside, we will derive a formula so we can take the integral above.

The total derivative is defined as
$$
d(uv) = udv + vdu
$$


After taking the integral of both sides, we can solve for a formula that gives the following
$$
\int d(uv) = \int udv + \int vdu
$$

$$
\int udv = uv - \int vdu
$$

The formula above is called *Integration by Parts*. We will make use of this formula by defining $u = \lambda x$ and $dv = e^{-\lambda x} dx$

This implies that $du = \lambda dx$ and $v= -\frac{1}{\lambda}e^{-\lambda x}$  
$$
E(X) = -\lim_{a \to \infty}[\lambda x \frac{1}{\lambda}e^{-\lambda x}]_0^a -  \lim_{b \to \infty}\int_0^b  -\frac{1}{\lambda}e^{-\lambda x}\lambda dx
$$

$$
E(X) = -\lim_{a \to \infty} [xe^{-\lambda x}]_0^a - \lim_{b \to \infty}\int_0^b -e^{-\lambda x}dx
$$

$$
E(X) = -\lim_{a \to \infty}(ae^{-\lambda a}) - \lim_{b \to \infty}[\frac{1}{\lambda}e^{-\lambda x}]_0^b
$$

$$
E(X) = 0 - \frac{1}{\lambda}[\lim_{b \to \infty}(e^{-\lambda b}) - e^{-0\lambda}]
$$

$$
E(X) = -\frac{1}{\lambda}(-1) = \frac{1}{\lambda}
$$

For the purposes of this lab, we will make the rate ($\lambda$) equal to 3. Which means we should expect our mean to be roughly equal to $\frac{1}{3}$.

#### Median

The median can be found by setting the CDF equal to $\frac{1}{2}$
$$
1- e^{-\lambda Median(X)} = \frac{1}{2}
$$

$$
e^{-\lambda Median(X)} = \frac{1}{2}
$$

$$
-\lambda Median(X) = \ln(\frac{1}{2})
$$

$$
Median(X) = \frac{\ln(2)}{\lambda}
$$

This shows that we should expect our median to be around $\frac{\ln(2)}{3} \approx 0.231$.

### Inverse Transform Sampling

Once we have a uniform distribution of values, we can then use these values to map to an exponential distribution. This is done through a technique called inverse transform sampling, the technique works as follows:

1. Generate a random number u from the standard uniform distribution
2. Compute the value of X such that F(X) = u
3. The value of X belongs to the distribution of F

Using these steps, we'll derive the exponential transform below.
$$
F(X) = 1 - e^{-\lambda x} = u
$$
Then proceeding to solve for X, we obtain the following.
$$
e^{-\lambda X} = 1 - u
$$

$$
-\lambda X = \ln(1 - u)
$$

$$
X = \frac{-\ln(1 - u)}{\lambda}
$$

With this formula, we can now find values for X which is a random variable that follows an exponential distribution given random uniform data $u$.

In this lab, we are looking at the exponential distribution with a rate of 3. Therefore, the probability mass function, the cumulative distribution function, and the exponential transform can be redefined as these respectively.
$$
f(x) = 3e^{-3x}
$$

$$
F(x) = 1 - e^{-3x}
$$

$$
X = \frac{-\ln(1 - u)}{3}
$$

### R Code

The R code makes use of the concepts above. The purpose of this code is to output the summary statistics, histograms, and Q-Q plots are used to compare the different methods.

First the LCM is executed four times with three different seed values. The LCM is used to create a uniform distribution of data that is then compared to the standard `runif` function in the R language.

Then, transformations of a LCM, `runif`, are executed and compared with the standard `rexp` to create an exponential distribution of data with $\lambda = 3$. 



## Results

### Uniform Distribution

For a small sample of 100 values, the data seems evenly distributed for all seeds and methods used.  The peaks and troughs are more pronounced in the LCM methods suggesting that the `runif` command creates more evenly distributed data than the LCM.  

Deviations from the mean and median are lowest for the LCM rather than the standard `runif` command with the exception of the LCM with the seed of 93463.

The Q-Q plots for all of the methods follow the Q-Q Line tightly and appear symmetric.

### Exponential Distribution

A bin size of 20 is used to make the histograms easily comparable to each other. One interesting thing to note is that in Figure XI, there is an observation located far out from the rest of the data. For the purpose of a histogram, which is to show us the shape of the distribution, this one far observation skews what we can see. Therefore the next figure, Figure XII  has that single outlier removed and shows the histogram of the rest of the data.

All of the histograms appear exponential in shape. Looking at the Q-Q plots, the LCM transformation and the `rexp` distribution of data fit closely to the QQ-Line. All of the Q-Q Plots have the points getting further away from the line as you get higher up in the percentiles. The `runif` transformation quantiles diverge from the line after about the 50th percentile.

Deviations from the mean and median were about the same for both transformed techniques (`runif` and LCM). The `rexp` command did better when it came to the deviation from the mean, but performed worse when it came to deviation from the median.

## Conclusion

The linear congruential methods performed better when it came to simulating the distribution than the standard R functions. It more accurately captured the median for both the standard uniform data, and the exponential data. Against the `runif` command, it also performed better at simulating the mean.

This can especially be seen when comparing the two transform techniques. The transformed LCM distribution of data followed the Q-Q line more tightly than the transformed `runif`.

I speculate that this is due to the seed value used. The Mersenne-Twist method performs better when the seed value doesn't have many zeros in it. Since the seed value is determined by the system time and process id, we don't know for sure if it's a proper input for the Mersenne-Twist. For the LCM, seeds were properly tested to make sure that it was co-prime with one of its parameters. This condition allowed proper seeds to work well with the LCM. 

Further research can be done on standardizing the seed values used across all the different pseudo random number generators and looking at the 6 other pseudo RNG that comes built into R. Changing the seed and random number generator can be achieved through the `set.seed` function.

## Appendix

### Figures

#### Figure I, Histogram of LCM Random Data with seed 55555

![](file:///home/rozek/Pictures/stat381lab2/hist55555.png)

#### Figure II, Q-Q Plot of LCM Random Data with seed 55555

![qqplot55555](/home/rozek/Pictures/stat381lab2/qqplot55555.png)

#### Figure III, Histogram of LCM Random Data with seed 93463

![hist93463](/home/rozek/Pictures/stat381lab2/hist93463.png)

#### Figure IV, Q-Q Plot of LCM Random Data with seed 93463

![q93463](/home/rozek/Pictures/stat381lab2/q93463.png)

#### Figure V, Histogram of LCM Random Data with seed 29345

![hist29345](/home/rozek/Pictures/stat381lab2/hist29345.png)

#### Figure VI, Q-Q Plot of LCM Random Data with seed 29345

![q29345](/home/rozek/Pictures/stat381lab2/q29345.png)



#### Figure VII, Histogram of LCM Random Data with seed 68237

![hist68237](/home/rozek/Pictures/stat381lab2/hist68237.png)

#### Figure VIII, Q-Q Plot of LCM Random Data with seed 68237

![q68237](/home/rozek/Pictures/stat381lab2/q68237.png)

#### Figure IX, Histogram of R Random Uniform Data

![histunif](/home/rozek/Pictures/stat381lab2/histunif.png)

#### Figure X, Q-Q Plot of R Random Uniform Data

![qunif](/home/rozek/Pictures/stat381lab2/qunif.png)

#### Figure XI, Histogram of Exponential Data from LCM Random

![histexplcm](/home/rozek/Pictures/stat381lab2/histexplcm.png)

#### Figure XII, Histogram of Exponential Data from LCM Random without Outlier Above 2

![histexplcm_nooutlier](/home/rozek/Pictures/stat381lab2/histexplcm_nooutlier.png)

#### Figure XIII, Q-Q Plot of Exponential Data from LCM Rnadom

![qexplcm](/home/rozek/Pictures/stat381lab2/qexplcm.png)

#### Figure XIV, Histogram of Exponential Data from R Random Uniform

![histexpunif](/home/rozek/Pictures/stat381lab2/histexpunif.png)

#### Figure XV, Q-Q Plot of Exponential Data from R Random Uniform

![qexpunif](/home/rozek/Pictures/stat381lab2/qexpunif.png)

#### Figure XVI, Histogram of R Generated Exponential Data

![histexp](/home/rozek/Pictures/stat381lab2/histexp.png)

#### Figure XVII, Q-Q Plot of R Generated Exponential Data

![qexp](/home/rozek/Pictures/stat381lab2/qexp.png)

### Tables

#### Table I, Uniform Distribution Sample Data

| Method              | Mean ($\bar{x}$) | Median ($\tilde{x}$) | $\mu - \bar{x}$ | $m - \tilde{x}$ |
| ------------------- | ---------------- | -------------------- | --------------- | --------------- |
| LCM with seed 55555 | 0.505            | 0.521                | -0.005          | -0.021          |
| LCM with seed 93463 | 0.452            | 0.402                | 0.048           | 0.098           |
| LCM with seed 29345 | 0.520            | 0.502                | -0.020          | -0.002          |
| LCM with seed 68237 | 0.489            | 0.517                | 0.011           | -0.017          |
| R Random Uniform    | 0.480            | 0.471                | 0.020           | 0.029           |

#### Table II, Exponential Distribution Sample Data

| Method          | Mean  | Median | $\mu - \bar{x}$ | $m - \tilde{x}$ |
| --------------- | ----- | ------ | --------------- | --------------- |
| LCM Transform   | 0.380 | 0.246  | -0.047          | -0.015          |
| RUnif Transform | 0.283 | 0.218  | 0.050           | 0.013           |
| R Exponential   | 0.363 | 0.278  | -0.030          | -0.047          |

### R Code

```R
library(ggplot2)
linear_congruential = function(seed) {
  a = 69069
  c = 0
  m = 2^31
  x = numeric(100)
  x[1] = seed
  for (i in 2:100) {
    x[i] = (a * x[i-1] + c) %% m 
  }
  xnew = x / (max(x) + 1)
  xnew
}

gcd = function(x,y) {
  r = x %% y;
  return(ifelse(r, gcd(y, r), y))
}
check_seed = function(seed) {
  if (gcd(seed, 2^31) == 1) {
    print(paste("The seed value of", seed, "is co-prime"))
  } else {
    print(paste("The seed value of", seed, "is NOT co-prime"))
  }
}

check_data = function(data, distribution, title) {
  print(paste("Currently looking at", title))
  print(summary(data))
  print(ggplot(data.frame(data), aes(x = data)) +
    geom_histogram(fill = 'white', color = 'black', bins = 10) +
    xlab("Date") +
    ylab("Frequency") + 
    ggtitle(paste("Histogram of", title)) +
    theme_bw())
  uqs = (1:100) / 100
  if (distribution == "Uniform") {
    qqplot(data, uqs, pch = 1, col = '#001155', main = paste("QQ Plot of", title), xlab = "Sample Data", ylab = "Theoretical Data")
    qqline(uqs, distribution = qunif, col="red", lty=2)
  } else if (distribution == "Exponential") {
    eqs = -log(1-uqs) / 3
    qqplot(data, eqs, pch = 1, col = '#001155', main = paste("QQ Plot of", title), xlab = "Sample Data", ylab = "Theoretical Data")
    qqline(eqs, distribution=function(p) { qexp(p, rate = 3)}, col="#AA0000", lty=2)
  }
}

seed1 = 55555
seed2 = 93463
seed3 = 29345
seed4 = 68237

check_seed(seed1)
lin_cong = linear_congruential(seed1)
check_data(lin_cong, "Uniform", paste("LCM Random Data with seed", seed1))

check_seed(seed2)
lin_cong2 = linear_congruential(seed2)
check_data(lin_cong2, "Uniform", paste("LCM Random Data with seed", seed2))

check_seed(seed3)
lin_cong3 = linear_congruential(seed3)
check_data(lin_cong3, "Uniform", paste("LCM Random Data with seed", seed3))

check_seed(seed4)
lin_cong4 = linear_congruential(seed4)
check_data(lin_cong4, "Uniform", paste("LCM Random Data with seed", seed4))

# Using the standard built-in R function
unif = runif(100, 0, 1)
check_data(unif, "Uniform", "R Random Uniform Data")

# Building exponential from linear congruence method
exp1 = -log(1 - lin_cong) / 3
check_data(exp1, "Exponential", "Exponential Data from LCM Random")

# Building exponential from runif
exp2 = -log(1 - unif) / 3
check_data(exp2, "Exponential", "Exponential Data from R Random Uniform")

# Building exponential from rexp
exp3 = rexp(100, rate = 3)
check_data(exp3, "Exponential", "R Generated Exponential Data")
```

