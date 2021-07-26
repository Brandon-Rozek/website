---
title: Week 4
showthedate: false
math: true
---

## Exponential Data

Suppose you're waiting for a bus that you think comes on average once every 10 minutes, but you're not sure exactly how often it comes.
$$
Y \sim Exp(\lambda)
$$
Your waiting time has a prior expectation of $\frac{1}{\lambda}$



It turns out the gamma distribution is conjugate for an exponential likelihood. We need to specify a prior, or a particular gamma in this case. If we think that the buses come on average every ten minutes, that's a rate of one over ten.
$$
prior_{mean} = \frac{1}{10}
$$
Thus, we'll want to specify a gamma distribution so that the first parameter divded by the second parameter is $\frac{1}{10}$

We can now think about our variability. Perhaps you specify
$$
\Gamma(100, 1000)
$$
This will indeed have a prior mean of $\frac{1}{10}$ and it'll have a standard deviation of $\frac{1}{100}$. If you want to have a rough estimate of our mean plus or minus two standard deviations then we have the following
$$
0.1 \pm 0.02
$$
Suppose that we wait for 12 minutes and a bus arrives. Now you want to update your posterior for $\lambda$ about how often this bus will arrive. 
$$
f(\lambda | y) \propto f(y|\lambda)f(\lambda)
$$

$$
f(\lambda | y) \propto \lambda e^{-\lambda y}\lambda^{\alpha - 1}e^{-\beta \lambda}
$$

$$
f(\lambda | y)  \propto \lambda^{(\alpha + 1) - 1}e^{-(\beta + y)\lambda}
$$

$$
\lambda | y \sim \Gamma(\alpha + 1, \beta + y)
$$

Plugging in our particular prior gives us a posterior for $\lambda$ which is
$$
\lambda | y \sim \Gamma(101, 1012)
$$
Thus our posterior mean is going to be $\frac{101}{1012} Which is equal to 0.0998.



This one observation doesn't contain a lot of data under this likelihood. When the bus comes and it takes 12 minutes instead of 10, it barely shifts our posterior mean up. One data point doesn't have a big impact here.



## Normal/Gaussian Data

Let's suppose the standard deviation or variance is known and we're only interested in learning about the mean. This is the situation that often arises in monitoring industrial production processes.
$$
X_i \sim N(\mu, \sigma^2)
$$
It turns out that the Normal distribution is conjugate for itself when looking for the mean parameter

Prior
$$
\mu \sim N(m_0,S_0^2)
$$

$$
f(\mu |x ) \propto f(x|\mu)f(\mu)
$$

$$
\mu | x \sim N(\frac{n\bar{x}/\sigma_0^2 + m_0/s_0^2}{n/\sigma_0^2 + 1/s_0^2}, \frac{1}{n/\sigma_0^2 + 1/s_0^2})
$$

Let's look at the posterior mean
$$
posterior_{mean} = \frac{n/\sigma_0^2}{n/\sigma_0^2 + 1/s_0^2}\bar{x} + \frac{1/s_0^2}{n/\sigma_0^2 + 1/s_0^2}
$$

$$
posterior_{mean} = \frac{n}{n + \sigma_0^2/s_0^2}\bar{x} + \frac{\sigma_0^2/s_0^2}{n + \sigma_0^2/s_0^2}
$$

Thus we see, that the posterior mean is a weighted average of the prior mean and the data mean. And indeed that the effective sample size for this prior is the ratio of the variance for the data to the variance in the prior.

This makes sense, because the larger the variance of the prior, the less information that's in it.

The marginal distribution for Y is 
$$
N(m_0, s_0^2 + \sigma^2)
$$

### When $\mu$ and $\sigma^2$  is unknown

$$
X_i | \mu, \sigma^2 \sim N(\mu, \sigma^2)
$$

A prior from $\mu$ conditional on the value for $\sigma^2$ 
$$
\mu | \sigma^2 \sim N(m, \frac{\sigma^2}{w})
$$
$w$ is going to be the ratio of $\sigma^2$ and some variance for the Normal distribution. This is the effective sample size of the prior.

Finally, the last step is to specify a prior for $\sigma^2$. The conjugate prior here is an inverse gamma distribution with parameters $\alpha$ and $\beta$.
$$
\sigma^2 \sim \Gamma^{-1}(\alpha, \beta)
$$
After many calculations... we get the posterior distribution
$$
\sigma^2 | x \sim \Gamma^{-1}(\alpha + \frac{n}{2}, \beta + \frac{1}{2}\sum_{i = 1}^n{(x-\bar{x}^2 + \frac{nw}{2(n+2)}(\bar{x} - m)^2)})
$$

$$
\mu | \sigma^2,x \sim N(\frac{n\bar{x}+wm}{n+w}, \frac{\sigma^2}{n + w})
$$

Where the posterior mean can be written as the weighted average of the prior mean and the data mean.
$$
\frac{n\bar{x}+wm}{n+w} = \frac{w}{n + w}m + \frac{n}{n + w}\bar{x}
$$
In some cases, we really only care about $\mu$. We want some inference on $\mu$ and we may want it such that it doesn't depend on $\sigma^2$. We can marginalize that $\sigma^2$ integrating it out. The posterior for $\mu$ marginally follows a $t$ distribution.
$$
\mu | x \sim t
$$
Similarly the posterior predictive distribution also is a $t$ distribution.

Finally, note that we can extend this in various directions, this can be extended to the multivariate normal case that requires matrix vector notations and can be extended in a hierarchial fashion if we want to specify priors for $m$, $w$ and $\beta$ 

## Non Informative Priors

We've seen examples of choosing priors that contain a significant amount of information. We've also seen some examples of choosing priors where we're attempting to not put too much information in to keep them vague.

Another approach is referred to as objective Bayesian statistics or inference where we explicitly try to minimize the amount of information that goes into the prior.

This is an attempt to have the data have maximum influence on the posterior

Let's go back to coin flipping
$$
Y_i \sim B(\theta)
$$
How do we minimize our prior information in $\theta$? One obvious intuitive approach is to say that all values of $\theta$ are equally likely. So we could have a piror for $\theta$ which follows a uniform distribution on the interval $[0, 1]$ 

Saying all values of $\theta$ are equally likely **seems** like it would have no information in it.

Recall however, that a $Uniform(0, 1)$ is the same as $Beta(1, 1)$ 

The effective sample size of a beta prior is the sum of its two parameters. So in this case, it has an effective sample size of 2. This is equivalent to data, with one head and one tail already in it.

So this is not a completely non informative prior.

We could think about a prior that has less information. For example $Beta(\frac{1}{2}, \frac{1}{2})$, this would have half as much information with an effective sample size of one.

We can take this even further. Think about something like $Beta(0.001, 0.001)$ This would have much less information, with the effective sample size fairly close to zero. In this case, the data would determine the posterior and there would be very little influence from the prior.

###Improper priors

Can we go even further? We can think of the limiting case. Let's think of $Beta(0,0)$, what would that look like? 
$$
f(\theta) \propto \theta^{-1}(1-\theta)^{-1}
$$
This is not a proper density. If you integrate this over $(0,1)$, you'll get an infinite integral, so it's not a true density in the sense of it not integrating to 1.

There's no way to normalize it, since it has an infinite integral. This is what we refer to as an improper prior.

It's improper in the sense that it doesn't have a proper density. But it's not necessarily imporper in the sense that we can't use it. If we collect data, we use this prior and as long as we observe one head and one tail, or **at least one success and one failure**. Then we can get a posterior
$$
f(\theta|y) \propto \theta^{y-1}(1-\theta)^{n-y-1} \sim Beta(y, n-y)
$$
With a posterior mean of $\frac{y}{n} =\hat{\theta}$, which you should recognize as the maximum likelihood estimate. So by using this improper prior, we get a posterior which gives us point estimates exactly the same as the frequentest approach.

But in this case, we can also think of having a full posterior. From this, we can make interval statements, probability statements, and we can actually find an interval and say that there's 95% probability that $\theta$ is in this interval. Which is not something you can do under the frequentest approach even though we may get the same exact interval.

### Statements about improper priors

Improper priors are okay as long as the posterior itself is proper. There may be some mathematical things that need to be checked and you may need to have certain restrictions on the data. In this case, we needed to make sure that we observed at least one head and one tail to get a proper posterior.

But as long as the posterior is proper, we can go forwards and do Bayesian inference even with an improper prior.

The second point is that for many problems there does exist a prior, typically an improper prior that will lead to the same point estimates as you would get under the frequentest paradigm. So we can get very similar results, results that are fully dependent on the data, under the Bayesian approach.

But in this case, we can also have continue to have a posterior and make posterior interval estimates and talk about posterior probabilities of the parameter.

### Normal Case

Another example is thinking about the normal case.
$$
Y_i \stackrel{iid}\sim N(\mu, \sigma^2)
$$
Let's start off by assuming that $\sigma^2$ is known and we'll just focus on the mean $\mu$.

We can think about a vague prior like before and say that 
$$
\mu \sim N(0, 1000000^2)
$$
This would just spread things out across the real line. That would be a fairly non informative prior covering a lot of possibilities. We can then think about taking the limit, what happens if we let the variance go to $\infty$. In that case, we're basically spreading out this distribution across the entire real number line. We can say that the density is just a constant across the whole real line.
$$
f(\mu) \propto 1
$$
This is an improper prior because if you integrate the real line you get an infinite answer. However, if we go ahead and find the posterior
$$
f(\mu|y) \propto f(y|\mu)f(\mu) \propto exp(-\frac{1}{2\sigma^2}\sum{(y_i - \mu)^2})(1)
$$

$$
f(\mu | y) \propto exp(-\frac{1}{2\sigma^2/n}(\mu - \bar{y})^2)
$$

$$
\mu | y \sim N(\bar{y}, \frac{\sigma^2}{n})
$$

This should look just like the maximum likelihood estimate.

### Unknown Variance

In the case that $\sigma^2$ is unknown, the standard non informative prior is
$$
f(\sigma^2) \propto \frac{1}{\sigma^2}
$$

$$
\sigma^2 \sim \Gamma^{-1}(0,0)
$$

This is an improper prior and it's uniform on the log scale of $\sigma^2$.

In this case, we'll end up with a posterior for $\sigma^2$
$$
\sigma^2|y \sim \Gamma^{-1}(\frac{n-1}{2}, \frac{1}{2}\sum{(y_i - \bar{y})^2})
$$
This should also look reminiscent of quantities we get as a frequentest. For example, the samples standard deviation

## Jeffreys Prior

Choosing a uniform prior depends upon the particular parameterization. 

Suppose I used a prior which is uniform on the log scale for $\sigma^2$
$$
f(\sigma^2) \propto \frac{1}{\sigma^2}
$$
Suppose somebody else decides, that they just want to put a uniform prior on $\sigma^2$ itself.
$$
f(\sigma^2) \propto 1
$$
These are both uniform on certain scales or certain parameterizations, but they are different priors. So when we compute the posteriors, they will be different as well.

 The key thing is that uniform priors are not invariant with respect to transformation. Depending on how you parameterize the problem, you can get different answers by using a uniform prior

One attempt to round this out is to use Jeffrey's Prior

Jeffrey's Prior is defined as the following
$$
f(\theta) \propto \sqrt{\mathcal{I(\theta)}}
$$
Where $\mathcal{I}(\theta)$ is the fisher information of $\theta$. In most cases, this will be an improper prior.

### Normal Data

For the example of Normal Data
$$
Y_i \sim N(\mu, \sigma^2)
$$

$$
f(\mu) \propto 1
$$

$$
f(\sigma^2) \propto \frac{1}{\sigma^2}
$$

Where $\mu$ is uniform and $\sigma^2$ is uniform on the log scale.

This prior will then be transformation invariant. We will end up putting the same information into the prior even if we use a different parameterization for the Normal.

### Binomial

$$
Y_i \sim B(\theta)
$$

$$
f(\theta) \propto \theta^{-\frac{1}{2}}(1-\theta)^{-\frac{1}{2}} \sim Beta(\frac{1}{2},\frac{1}{2})
$$

This is a rare example of where the Jeffreys prior turns out to be a proper prior.

You'll note that this prior actually does have some information in it. It's equivalent to an effective sample size of one data point. However, this information will be the same, not depending on the parameterization we use.

In this case, we have $\theta$ as a probability, but another alternative which is sometimes used is when we model things on a logistics scale.

By using the Jeffreys prior, we'll maintain the exact same information.

### Closing information about priors

Other possible approaches to objective Bayesian inference includes priors such as reference priors and maximum entropy priors.

A related concept to this is called empirical Bayesian analysis. The idea in empirical Baye's is that you use the data to help inform your prior; such as by using the mean of the data to set the mean of the prior distribution. This approach often leads to reasonable point estimates in your posterior. However, it's sort of cheating since you're using your data twice and as a result may lead to improper uncertainty estimates.

## Fisher Information

The Fisher information (for one parameter) is defined as
$$
\mathcal{I}(\theta) = E[(\frac{d}{d\theta}log{(f(X|\theta))})^2]
$$
Where the expectation is taken with respect to $X$ which has PDF $f(x|\theta)$. This quantity is useful in obtaining estimators for $\theta$ with good properties, such as low variance. It is also the basis for Jeffreys prior.

**Example:** Let $X | \theta \sim N(\theta, 1)$. Then we have
$$
f(x|\theta) = \frac{1}{\sqrt{2\pi}}exp[-\frac{1}{2}(x-\theta)^2]
$$

$$
\log{(f(x|\theta))} = -\frac{1}{2}\log{(2\pi)}-\frac{1}{2}(x-\theta)^2
$$

$$
(\frac{d}{d\theta}log{(f(x|\theta))})^2 = (x-\theta)^2
$$

and so $\mathcal{I}(\theta) = E[(X - \theta)^2] = Var(X) = 1$

## Linear Regression

###Brief Review of Regression

Recall that linear regression is a model for predicting a response or dependent variable ($Y$, also called an output) from one or more covariates or independent variables ($X$, also called explanatory variables, inputs, or features). For a given value of a single $x$, the expected value of $y$ is
$$
E[y] = \beta_0 + \beta_1x
$$
or we could say that $Y \sim N(\beta_0 + \beta_1x, \sigma^2)$. For data $(x_1, y_1), \dots , (x_n, y_n)$, the fitted values for the coefficients, $\hat{\beta_0}$ and $\hat{\beta_1}$ are those that minimize the sum of squared errors $\sum_{i = 1}^n{(y_i - \hat{y_i})^2}$, where the predicted values for the response are $\hat{y} = \hat{\beta_0}  + \hat{\beta_1}x$. We can get these values from R. These fitted coefficients give the least-squares line for the data.

This model extends to multiple covariates, with one $\beta_j$ for each $k$ covariates
$$
E[y_i] = \beta_0 + \beta_1x_{i1} + \dots + \beta_kx_{ik}
$$
Optionally, we can represent the multivariate case using vector-matrix notation.

### Conjugate Modeling

In the Bayesian framework, we treat the $\beta$ parameters as unknown, put a prior on them, and then find the posterior. We might treat $\sigma^2$ as fixed and known, or we might treat it as an unknown and also put a prior on it. Because the underlying assumption of a regression model is that the errors are independent and identically normally distributed with mean $0$ and variance $\sigma^2$, this defines a normal likelihood.

#### $\sigma^2$ known

Sometimes we may know the value of the error variance $\sigma^2$. This simplifies calculations. The conjugate prior for the $\beta$'s is a normal prior. In practice, people typically use a non-informative prior, i.e., the limit as the variance of the normal prior goes to infinity, which has the same mean as the standard least-squares estimates. If we are only estimating $\beta$ and treating $\sigma^2$ as known, then the posterior for $\beta$ is a (multivariate) normal distribution. If we just have a single covariate, then the posterior for the slope is
$$
\beta_1 | y \sim N(\frac{\sum_{i = 1}^n{(x_i-\bar{x})(y_i - \bar{y})}}{\sum_{i=1}^n{(x_i-\bar{x})^2}}, \frac{\sigma^2}{\sum_{i=1}^n{(x_i - \bar{x})^2}})
$$
If we have multiple covariates, then using a matrix-vector notation, the posterior for the vector of coefficients is
$$
\beta | y \sim N((X^tX)^{-1}X^ty, (X^tX)^{-1}\sigma^2)
$$
where $X$ denotes the design matrix and $X^t$ is the transpose of $X$. The intercept is typically included in $X$ as a column of $1$'s. Using an improper prior requires us to have at least as many data points as we have parameters to ensure that the posterior is proper.

#### $\sigma^2$ Unknown

If we treat both $\beta$ and $\sigma^2$ as unknown, the standard prior is the non-informative Jeffreys prior, $f(\beta, \sigma^2) \propto \frac{1}{\sigma^2}$. Again, the posterior mean for $\beta$ will be the same as the standard least-squares estimates. The posterior for $\beta$ conditional on $\sigma^2$ is the same normal distributions as when $\sigma^2$ is known, but the marginal posterior distribution for $\beta$, with $\sigma^2$ integrated out is a $t$ distribution, analogous to the $t$ tests for significance in standard linear regression. The posterior $t$ distribution has mean $(X^tX)^{-1}X^ty$ and scale matrix (related to the variance matrix) $s^2(X^tX)^{-1}$, where $s^2 = \sum_{i = 1}^n{(y_i - \hat{y_i})^2/(n - k - 1)}$. The posterior distribution for $\sigma^2$ is an inverse gamma distribution
$$
\sigma^2 | y \sim \Gamma^{-1}(\frac{n - k - 1}{2}, \frac{n - k - 1}{2}s^2)
$$
In the simple linear regression case (single variable), the marginal posterior for $\beta$ is a $t$ distribution with mean $\frac{\sum_{i = 1}^n{(x_i-\bar{x})(y_i - \bar{y})}}{\sum_{i=1}^n{(x_i-\bar{x})^2}}$ and scale $ \frac{s^2}{\sum_{i=1}^n{(x_i - \bar{x})^2}}$. If we are trying to predict a new observation at a specified input $x^*$, that predicted value has a marginal posterior predictive distribution that is a $t$ distribution, with mean $\hat{y} = \hat{\beta_0} + \hat{\beta_1}x^*$ and scale $se_r\sqrt{1 + \frac{1}{n} + \frac{(x^* - \bar{x})^2}{(n - 1)s_x^2}}$. $se_r$ is the residual standard error of the regression, which can be found easily in R. $s_x^2$ is the sample variance of $x$. Recall that the predictive distribution for a new observation has more variability than the posterior distribution for $\hat{y}$ , because individual observations are more variable than the mean.

## Linear Regression

### Single Variable Regression

We'll be looking at the Challenger dataset. It contains 23 past launches where it has the temperature at the day of launch and the O-ring damage index

http://www.randomservices.org/random/data/Challenger2.txt
Read in the data

```R
oring=read.table("http://www.randomservices.org/random/data/Challenger2.txt",
                 header=T)
# Note that attaching this masks T which is originally TRUE
attach(oring)
```

Now we'll see the plot

```R
plot(T, I)
```

![Challenger](files/courses/BayesianStatistics/Challenger.png)

Fit a linear model

```R
oring.lm=lm(I~T)
summary(oring.lm)
```

Output of the summary

```
Call:
lm(formula = I ~ T)

Residuals:
    Min      1Q  Median      3Q     Max 
-2.3025 -1.4507 -0.4928  0.7397  5.5337 

Coefficients:
            Estimate Std. Error t value Pr(>|t|)
(Intercept) 18.36508    4.43859   4.138 0.000468
T           -0.24337    0.06349  -3.833 0.000968
               
(Intercept) ***
T           ***
---
Signif. codes:  
0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1

Residual standard error: 2.102 on 21 degrees of freedom
Multiple R-squared:  0.4116,	Adjusted R-squared:  0.3836 
F-statistic: 14.69 on 1 and 21 DF,  p-value: 0.0009677
```

Add the fitted line into the scatterplot

```R
lines(T,fitted(oring.lm))     
```

![challengerfitted](files/courses/BayesianStatistics/challengerfitted.png)

Create a 95% posterior interval for the slope

```R
-0.24337 - 0.06349*qt(.975,21)
# [1] -0.3754047
-0.24337 + 0.06349*qt(.975,21)
# [1] -0.1113353
```

**Note:** These are the same as the frequentest confidence intervals

If the challenger launch was at 31 degrees Fahrenheit, how much O-Ring damage would we predict?

```R
coef(oring.lm)[1] + coef(oring.lm)[2]*31  
# [1] 10.82052 
```

Let's make our posterior prediction interval

```R
predict(oring.lm,data.frame(T=31),interval="predict")
```

Output of `predict`

```
       fit      lwr      upr
1 10.82052 4.048269 17.59276
```

We can calculate the lower bound through the following formula

```R
10.82052-2.102*qt(.975,21)*sqrt(1+1/23+((31-mean(T))^2/22/var(T)))
```

What's the posterior probability that the damage index is greater than zero?

```R
1-pt((0-10.82052)/(2.102*sqrt(1+1/23+((31-mean(T))^2/22/var(T)))),21)
```

### Multivariate Regression

We're looking at Galton's seminal data predicting the height of children from the height of the parents

http://www.randomservices.org/random/data/Galton.txt
Read in the data

```R
heights=read.table("http://www.randomservices.org/random/data/Galton.txt",
                   header=T)
attach(heights)
```

What are the columns in the dataset?

```R
names(heights)
# [1] "Family" "Father" "Mother" "Gender" "Height" "Kids"  
```

Let's look at the relationship between the different variables

```R
pairs(heights)
```

![heightpairs](files/courses/BayesianStatistics/heightpairs.png)

First let's start by creating a linear model taking all of the columns into account

```R
summary(lm(Height~Father+Mother+Gender+Kids))
```

Output of `summary`

```
Call:
lm(formula = Height ~ Father + Mother + Gender + Kids)

Residuals:
    Min      1Q  Median      3Q     Max 
-9.4748 -1.4500  0.0889  1.4716  9.1656 

Coefficients:
            Estimate Std. Error t value Pr(>|t|)
(Intercept) 16.18771    2.79387   5.794 9.52e-09
Father       0.39831    0.02957  13.472  < 2e-16
Mother       0.32096    0.03126  10.269  < 2e-16
GenderM      5.20995    0.14422  36.125  < 2e-16
Kids        -0.04382    0.02718  -1.612    0.107
               
(Intercept) ***
Father      ***
Mother      ***
GenderM     ***
Kids           
---
Signif. codes:  
0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1

Residual standard error: 2.152 on 893 degrees of freedom
Multiple R-squared:  0.6407,	Adjusted R-squared:  0.6391 
F-statistic: 398.1 on 4 and 893 DF,  p-value: < 2.2e-16
```

As you can see here, the `Kids` column is not significant. Let's look at a model with it removed.

```R
summary(lm(Height~Father+Mother+Gender))
```

Output of `summary`

```
Call:
lm(formula = Height ~ Father + Mother + Gender)

Residuals:
   Min     1Q Median     3Q    Max 
-9.523 -1.440  0.117  1.473  9.114 

Coefficients:
            Estimate Std. Error t value Pr(>|t|)
(Intercept) 15.34476    2.74696   5.586 3.08e-08
Father       0.40598    0.02921  13.900  < 2e-16
Mother       0.32150    0.03128  10.277  < 2e-16
GenderM      5.22595    0.14401  36.289  < 2e-16
               
(Intercept) ***
Father      ***
Mother      ***
GenderM     ***
---
Signif. codes:  
0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1

Residual standard error: 2.154 on 894 degrees of freedom
Multiple R-squared:  0.6397,	Adjusted R-squared:  0.6385 
F-statistic:   529 on 3 and 894 DF,  p-value: < 2.2e-16
```

This model looks good, let's go ahead and save it to a variable

```R
heights.lm=lm(Height~Father+Mother+Gender)
```

From this we can tell that for each extra inch of height in a father is correlated with an extra 0.4 inches extra to the height of a child.

We can also tell that each extra inch of height in a mother is correlated with an extra 0.3 inches extra to the height of the child.

A male child is on average 5.2 inches taller than a female child.

Let's create a 95% posterior interval for the difference in height by gender

```R
5.226 - 0.144*qt(.975,894)
# [1] 4.943383 
5.226 + 0.144*qt(.975,894)
# [1] 5.508617
```

Let's make a posterior prediction interval for a male and female with a father whose 68 inches and a mother whose 64 inches.

```R
predict(heights.lm,data.frame(Father=68,Mother=64,Gender="M"),
        interval="predict")

#       fit      lwr     upr
# 1 68.75291 64.51971 72.9861
```

```R
predict(heights.lm,data.frame(Father=68,Mother=64,Gender="F"),
        interval="predict")

#       fit      lwr      upr
# 1 63.52695 59.29329 67.76062
```



## What's next?

This concludes this course, if you want to go further with Bayesian statistics, the next topics to explore would be hierarchal modeling and fitting of non conjugate models with Markov Chain Monte Carlo or MCMC.
