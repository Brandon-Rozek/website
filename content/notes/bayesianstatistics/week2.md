---
title: Week 2
showthedate: false
math: true
---

Under the frequentest paradigm, you view the data as a random sample from some larger, potentially hypothetical population. We can then make probability statements i.e, long-run frequency statements based on this larger population.

## Coin Flip Example (Central Limit Theorem)

Let's suppose we flip a coin 100 times and we get 44 heads and 56 tails.
$$
n = 100
$$
We can view these 100 flips as a random sample from a much larger infinite hypothetical population of flips from this coin.

Let's say that each flip follows a Bournelli distribution with some probability p. In this case $p$ is unknown, but we're assuming it's fixed because we have a particular physical coin.

We can ask what's our best estimate of the probability of getting a head, or an estimate of $p$. We can also ask about how confident we are about that estimate.

Let's start by applying the Central Limit Theorem. The Central Limit Theorem states that the sum of 100 flips will follow approximately a Normal distribution with mean 100p and variance 100p(1-p)
$$
\sum^n_{i=1}{x_i} \sim N(np, np(1-p))
$$

$$
\sum_{i = 1}^{100}{x_i} \sim N(100p, 100p(1-p))
$$

By the properties of a Normal distribution, 95% of the time we'll get a result within 1.96 standard deviations of the mean. Our estimate is $100\hat{p}$ and our error is 1.96 times the standard deviation.
$$
n\hat{p} \pm 1.96\sqrt{n\hat{p}(1-\hat{p})}
$$

$$
100\hat{p} \pm 1.96\sqrt{100\hat{p}(1-\hat{p})}
$$

This is referred to as a Confidence Interval. Confidence Intervals are commonly abbreviated as CI. In our example $\hat{p} = \frac{44}{n} = \frac{44}{100}$. Therefore, the 95% Confidence Interval in the true number of heads after flipping a coin 100 times is:
$$
100(.44) \pm 1.96\sqrt{100(.44)(1-.44)}
$$

$$
44 \pm 1.96\sqrt{44(.56)}
$$

$$
44\pm 1.96\sqrt{24.64}
$$

$$
(34.27, 53.73)
$$

We can divide this by 100 to get the 95% Confidence Interval for $p$
$$
(0.34, 0.53)
$$
Let's step back and ask, what does it mean when I say we're 95% confident?

Under the frequentest paradigm, what this means is we have to think back to our infinite hypothetical sequence of events. So if we were to repeat this trial an infinite number of times, or an arbitrary large number of times. Each time we create a confidence interval based on the data we observe, than on average 95% of the intervals we make will contain the true value of p.

On the other hand, we might want to know something about this particular interval. Does this interval contain the true p? What's the probability that this interval contains a true p? Well, we don't know for this particular interval. But under the frequentest paradigm, we're assuming that there is a fixed answer for p. Either p is in that interval or it's not in that interval. The probability that p is in that interval is either 0 or 1.

## Example: Heart Attack Patients (Maximum Likelihood)

Consider a hospital where 400 patients are admitted over a month for heart attacks, and a month later 72 of them have died and 328 of them have survived.

We can ask, what's our estimate of the mortality rate?

Under the frequentest paradigm, we must first establish our reference population. What do we think our reference population is here? One possibility is we could think about heart attack patients in the region.

Another reference population we can think about is heart attack patients that are admitted to this hospital, but over a longer period of time. 

Both of these might be reasonable attempts, but in this case our actual data are not random sample from either of those populations. We could sort of pretend they are and move on, or we could also try to think harder about what a random sample situation might be. We can think about all the people in the region who might possibly have a heart attack and might possibly get admitted to this hospital.

It's a bit of an odd hypothetical situation, and so there are some philosophical issues with the setup of this whole problem with the frequentest paradigm, In any case, let's forge forward and think about how we might do some estimation.

Moving on, we can say each patient comes from a Bernoulli distribution with an unknown parameter $\theta$. 
$$
Y_i \sim B(\theta)
$$

$$
P(Y_i = 1) = \theta
$$

In this case, let's call the "success" a mortality. 

The probability density function for the entire set of data we can write in vector form. Probability of all the Y's take some value little y given a value of theta.
$$
P(Y = y | \theta) = P(Y_1 = y_1, Y_2, = y_2,\dots, Y_n=y_n|\theta)
$$
*Since we're viewing these as independent events*, then the probability of each of these individual ones we can write in product notation.
$$
P(Y = y | \theta) = P(Y_1 = y_1|\theta)\dots P(Y_n = y_n | \theta)
$$

$$
P(Y = y | \theta) = \prod_{i = 1}^n{P(Y_i =y_i | \theta)} = \prod_{i = 1}^n{(\theta^{y_i}(1-\theta)^{1-y_i})}
$$

This is the probability of observing the actual data that we collected, conditioned on a value of the parameter $\theta$.  We can now think about this expression as a function of theta. This is a concept of a likelihood.
$$
L(\theta|y) = \prod_{i = 1}^n{(\theta^{y_i}(1-\theta)^{1-y_i})}
$$
It looks like the same function, but here it is a function of y given $\theta$. And now we're thinking of it as a function of $\theta$ given y.

This is not a probability distribution anymore, but it is still a function for $\theta$.

One we to estimate $\theta$ is that we choose the $\theta$ that gives us the largest value of the likelihood. It makes the data the most likely to occur for the particular data we observed.

This is referred to as the maximum likelihood estimate (MLE),

We're trying to find the $\theta$ that maximizes the likelihood.

In practice, it's usually easier to maximize the natural logarithm of the likelihood, commonly referred to as the log likelihood.
$$
\mathcal{L}(\theta) = \log{L(\theta|y)}
$$
Since the logarithm is a monotonic function, if we maximize the logarithm of the function, we also maximize the original function.
$$
\mathcal{L(\theta)} = \log{\prod_{i = 1}^n{(\theta^{y_i}(1-\theta)^{1-y_i})}}
$$

$$
\mathcal{L}(\theta) = \sum_{i = 1}^n{\log{(\theta^{y_i}(1-\theta)^{1-y_i})}}
$$

$$
\mathcal{L}(\theta) = \sum_{i = 1}^n{(\log{(\theta^{y_i}})  + \log{(1-\theta)^{1-y_i}})}
$$

$$
\mathcal{L}(\theta) = \sum_{i = 1}^n{(y_i\log{\theta} + (1 - y_i)\log{(1-\theta)})}
$$

$$
\mathcal{L}(\theta) = \log{\theta}\sum_{i  = 1}^n{y_i} + \log{(1-\theta)}\sum_{i = 1}^n{(1-y_i)}
$$

How do we find the theta that maximizes this function? Recall from calculus that we can maximize a function by taking the derivative and setting it equal to 0.
$$
\mathcal{L}^\prime(\theta) = \frac{1}{\theta}\sum{y_i} - \frac{1}{1-\theta}\sum{(1 - y_i)}
$$
Now we need to set it equal to zero and solve for $\hat{\theta}$
$$
\frac{\sum{y_i}}{\hat{\theta}} = \frac{\sum{(1-y_i)}}{1-\hat{\theta}}
$$

$$
\hat{\theta}\sum{(1-y_i)} = (1-\hat{\theta})\sum{y_i}
$$

$$
\hat{\theta}\sum{(1-y_i)} + \hat{\theta}\sum{y_i} = \sum{y_i}
$$

$$
\hat{\theta}(\sum^n{(1 - y_i + y_i)}) = \sum{y_i}
$$

$$
\hat{\theta} = \frac{1}{n}\sum{y_i} = \hat{p} = \frac{72}{400} = 0.18
$$

Maximum likelihood estimators have many desirable mathematical properties. They're unbiased, they're consistent, and they're invariant.

In general, under certain regularity conditions, we can say that the MLE is approximately normally distributed with mean at the true value of $\theta$ and the variance $\frac{1}{I(\hat{\theta})}$ where $I(\hat{\theta})$ is the Fisher information at the value of $\hat{\theta}$. The Fisher information is a measure of how much information about $\theta$ is in each data point.
$$
\hat{\theta} \sim N(\theta, \frac{1}{I(\hat{\theta})})
$$
For a Bernoulli random variable, the Fisher information turns out to be
$$
I(\theta) = \frac{1}{\theta(1-\theta)}
$$
So the information is larger, when theta is near zero or near one, and it's the smallest when theta is near one half.

This makes sense, because if you're flipping a coin, and you're getting a mix of heads and tails, that tells you a little bit less than if you're getting nearly all heads or nearly all tails.

## Exponential Likelihood Example

Let's say $X_i$ are distributed so
$$
X_i \sim Exp(\lambda)
$$
Let's say the data is independent and identically distributed, therefore making the overall density function
$$
f(x|\lambda) = \prod_{i = 1}^n{\lambda e^{-\lambda x_i}}
$$

$$
f(x|\lambda) = \lambda^ne^{-\lambda \sum{x_i}}
$$

Now the likelihood function is
$$
L(\lambda|x) = \lambda^n e^{-\lambda \sum{x_i}}
$$

$$
\mathcal{L}(\lambda) = n\ln{\lambda} - \lambda\sum{x_i}
$$

Taking the derivative
$$
\mathcal{L}^\prime(\lambda) = \frac{n}{\lambda} - \sum{x_i}
$$
Setting this equal to zero
$$
\frac{n}{\hat{\lambda}} =\sum{x_i}
$$

$$
\hat{\lambda} = \frac{n}{\sum{x_i}} = \frac{1}{\bar{x}}
$$

## Uniform Distribution

$$
X_i \sim U[0, \theta]
$$

$$
f(x|\theta) = \prod_{i = 1}^n{\frac{1}{\theta}I_{0 \le x_i \le \theta}}
$$

Combining all the indicator functions, for this to be a 1, each of these has to be true. These are going to be true if all the observations are bigger than 0, as in the minimum of the x is bigger than or equal to 0. The maximum of the x's is also less than or equal to $\theta$.
$$
L(\theta|x) = \theta^{-1} I_{0\le min(x_i) \le max(x_i) \le \theta}
$$

$$
L^\prime(\theta) = -n\theta^{-(n + 1)}I_{0 \le min(x_i) \le max(x_i)\le \theta}
$$

So now we can ask, can we set this equal to zero and solve for $\theta$? Well it turns out, this is not equal to zero for any $\theta$ positive value. We need $\theta$ to be strictly larger than zero.

However, we can also note that for $\theta$ positive, this will always be negative. The derivative is negative, that says this is a decreasing function. So this funciton will be maximized when we pick $\theta$ as small as possible. What's the smallest possible value of $\theta$ we can pick? Well we need in particular for $\theta$ to be larger than all of the $X_i$ . And so, the maximum likelihood estimate is the maximum of $X_i$
$$
\hat{\theta} = max(x_i)
$$

## Products of Indicator Functions

Because 0 * 1 = 0, the product of indicator functions can be combined into a single indicator function with a modified condition.

**Example**: $I_{x < 5} * I_{x \ge 0} = I_{0 \le x < 5}$ 

**Example**: $\prod_{i = 1}^n{I_{x_i < 2}} = I_{x_i < 2 for all i} = I_{max(x_i)  < 2}$

## Introduction to R

R has some nice functions that one can use for analysis

`mean(z)` gives the mean of some row vector $z$

`var(z)` reports the variance of some row vector

`sqrt(var(z))` gives the standard deviation of some row vector

`seq(from=0.1, to = 0.9, by = 0.1)` creates a vector that starts from $0.1$ and goes to $0.9$ incrementing by $0.1$

```R
seq(from=0.1, to = 0.9, by = 0.1)
[1] 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8 0.9
seq(1, 10)
[1] 1 2 3 4 5 6 7 8 9 10
```

`names(x)` gives the names of all the columns in the dataset.

```R
names(trees)
[1] "Girth"  "Height"  "Volume"
```

`hist(x)` provides a histogram based on a vector

The more general `plot` function tries to guess at which type of plot to make. Feeding it two numerical vectors will make a scatter plot.

The R function `pairs` takes in a data frame and tries to make all possible Pairwise scatterplots for the dataset. 

The `summary` command gives the five/six number summary (minimum, first quartile, median, mean,  third quartile, maximum)

## Plotting the likelihood function in R

Going back to the hospital example

```R
## Likelihood function
likelihood = function(n, y, theta) {
  return(theta^y * (1 - theta)^(n - y))
}
theta = seq(from = 0.01, to = 0.99, by = 0.01)
plot(theta, likelihood(400, 72, theta))
```

You can also do this with log likelihoods. This is typically more numerically stable to compute

```R
loglike = function(n, y, theta) {
  return(y * log(theta) + (n - y) * log(1 - theta))
}
plot(theta, loglike(400, 72, theta))
```

Having these plotted as points makes it difficult to see, let's plot it as lines

```R
plot(theta, loglike(400, 72, theta), type = "l")
```



## Cumulative Distribution Function

The cumulative distribution function (CDF) exists for every distribution. We define it as $F(x) = P(X \le x)$ for random variable $X$. 

If $X$ is discrete-valued, then the CDF is computed with summation $F(x) = \sum_{t = -\infty}^x {f(t)}$. where $f(t) = P(X = t)$ is the probability mass function (PMF) which we've already seen.

If $X$ is continuous, the CDF is computed with an integral $F(x) = \int_{-\infty}^x{f(t)dt}$

The CDF is convenient for calculating probabilities of intervals. Let $a$ and $b$ be any real numbers with $a < b$. Then the probability that $X$ falls between $a$ and $b$ is equal to $P(a < X < b) = P(X \le b) - P(X \le a) = F(b) - F(a)$  



## Quantile Function

The CDF takes a value for a random variable and returns a probability. Suppose instead we start with a number between $0$ and $1$, which we call $p$, and we wish to find a value $x$ so that $P(X \le x) = p$. The value $x$ which satisfies this equation is called the $p$ quantile. (or $100p$ percentile) of the distribution of $X$.



## Probability Distributions in R

Each of the distributions introduced in Lesson 3 have convenient functions in R which allow you to evaluate the PDF/PMF, CDF, and quantile functions, as well as generate random samples from the distribution. To illustrate, Table I list these functions for the normal distribution

| Function             | What it does                             |
| -------------------- | ---------------------------------------- |
| `dnorm(x, mean, sd)` | Evaluate the PDF at $x$ (mean = $\mu$ and sd = $\sqrt{\sigma^2}$) |
| `pnorm(q, mean, sd)` | Evaluate the CDF at $q$                  |
| `qnorm(p, mean, sd)` | Evaluate the quantile function at $p$    |
| `rnorm(n, mean, sd)` | Generate $n$ pseudo-random samples from the normal distribution |

These four functions exist for each distribution where `d...` function evaluates the density/mass, `p...` evaluates the CDF, `q...` evaluates the quantile, and `r...` generates a sample. Table 2 lists the `d...` functions for some of the most popular distributions. The `d` can be replaced with `p`, `q`, or `r` for any of the distributions, depending on what you want to calculate.

For details enter `?dnorm` to view R's documentation page for the Normal distribution. As usual , replace the `norm` with any distribution to read the documentation for that distribution.

| Distribution           | Function                   | Parameters                           |
| ---------------------- | -------------------------- | ------------------------------------ |
| $Binomial(n,p)$        | `dbinom(x, size, prob)`    | size = $n$, prob = $p$               |
| $Poisson(\lambda)$     | `dpois(x, lambda)`         | lambda = $\lambda$                   |
| $Exp(\lambda)$         | `dexp(x, rate)`            | rate = $\lambda$                     |
| $Gamma(\alpha, \beta)$ | `dgamma(x, shape, rate)`   | shape = $\alpha$, rate = $\beta$     |
| $Uniform(a, b)$        | `dunif(x, min, max)`       | min = $a$, max = $b$                 |
| $Beta(\alpha, \beta)$  | `dbeta(x, shape1, shape2)` | shape1 = $\alpha$, shape2 = $\beta$  |
| $N(\mu, \sigma^2)$     | `dnorm(x, mean, sd)`       | mean = $\mu$, sd = $\sqrt{\sigma^2}$ |
| $t_v$                  | `dt(x, df)`                | df = $v$                             |

## Two Coin Example

Suppose your brother has a coin which you know to be loaded so that it comes up heads 70% of the time. He then comes to you with some coin, you're not sure which one and he wants to make a bet with you. Betting money that it's going to come up heads.

You're not sure if it's the loaded coin or if it's just a fair one. So he gives you a chance to flip it 5 times to check it out.

You flip it five times and get 2 heads and 3 tails. Which coin do you think it is and how sure are you about that?

We'll start by defining the unknown parameter $\theta$, this is either that the coin is fair or it's a loaded coin.
$$
\theta = \{fair ,loaded\}
$$

$$
X \sim Bin(5, ?)
$$

$$
f(x|\theta) = \begin{cases} 
      {5 \choose x}(\frac{1}{2})^5            & \theta = fair \\
      {5 \choose x} (.7)^x (.3)^{5 - x}       & \theta = loaded\\
   \end{cases}
$$

We can also rewrite $f(x|\theta)$ with indicator functions
$$
f(x|\theta) = {5\choose x}(.5)^5I_{\{\theta= fair\}} + {5 \choose x}(.7)^x(.3)^{5 - x}I_{\{\theta = loaded\}}
$$
In this case, we observed that $x = 2$ 
$$
f(\theta | x = 2) = \begin{cases} 
	0.3125 & \theta = fair \\
	0.1323 & \theta = loaded
\end{cases}
$$
MLE $\hat{\theta} = fair$ 

That's a good point estimate, but then how do we answer the question, how sure are you?

This is not a question that's easily answered in the frequentest paradigm. Another question is that we might like to know what is the probability that theta equals fair, give, we observe two heads.
$$
P(\theta = fair|x = 2) = ?
$$
In the frequentest paradigm, the coin is a physical quantity. It's a fixed coin, and therefore it has a fixed probability of coining up heads. It is either the fair coin, or it's the loaded coin.
$$
P(\theta = fair) = \{0,1\}
$$

### Bayesian Approach to the Problem

An advantage of the Bayesian approach is that it allows you to easily incorporate prior information, when you know something in advance of the looking at the data. This is difficult to do under the Frequentest paradigm.

In this case, we're talking about your brother. You probably know him pretty well. So suppose you think that before you've looked at the coin, there's a 60% probability that this is the loaded coin.

This case, we put this into our prior. Our prior is that the probability the coin is loaded is 0.6. We can update our prior with the data to get our posterior beliefs, and we can do this using the bayes theorem.

Prior: $P(loaded) = 0.6$
$$
f(\theta|x) = \frac{f(x|\theta)f(\theta)}{\sum_\theta{f(x|\theta)f(\theta)}}
$$

$$
f(\theta|x) = \frac{{5\choose x} [(\frac{1}{2})^5(.4)I_{\{\theta = fair\}} + (.7)^x (.3)^{5-x}(.6)I_{\{\theta = loaded\}}  ] }
{{5\choose x} [(\frac{1}{2})^5(.4) + (.7)^x (.3)^{5-x}(0.6)  ] }
$$

$$
f(\theta|x=2)= \frac{0.0125I_{\{\theta=fair\}}  + 0.0079I_{\{\theta=loaded\}} }{0.0125+0.0079}
$$

$$
f(\theta|x=2) = 0.612I_{\{\theta=fair\}} + 0.388I_{\{\theta = loaded\}}
$$

As you can see in the calculation here, we have the likelihood times the prior in the numerator, and in the denominator, we have a normalizing constant, so that when we divide by this, we'll get answer that add up to one. These numbers match exactly in this case, because it's a very simple problem. But this is a concept that goes on, what's in the denominator here is always a normalizing constant.
$$
P(\theta = loaded | x = 2) = 0.388
$$
This here updates our beliefs after seeing some data about what the probability might be.

We can also examine what would happen under different choices of prior.
$$
P(\theta = loaded) = \frac{1}{2} \implies P(\theta = loaded | x = 2) = 0.297
$$

$$
P(\theta = loaded) = 0.9 \implies P(\theta = loaded | x = 2) = 0.792
$$

In this case, the Bayesian approach is inherently subjective. It represents your own personal perspective, and this is an important part of the paradigm. If you have a different perspective, you will get different answers, and that's okay. It's all done in a mathematically vigorous framework, and it's all mathematically consistent and coherent.

And in the end, we get results that are interpretable

## Continuous Bayes

$$
f(\theta | y) = \frac{f(y | \theta)f(\theta)}{f(y)} = \frac{f(y|\theta)f(\theta)}{\int{f(y|\theta)f(\theta)d\theta}} = \frac{likelihood * prior}{normalization} \propto likelihood * prior
$$

In practice, sometimes this integral can be a pain to compute. And so, we may work with looking at saying this is proportional to the likelihood times the prior. And if we can figure out what this looks like and just put the appropriate normalizing constant on at the end, we don't necessarily have to compute this integral.



So for example, suppose we're looking at a coin and it has unknown probability $\theta$ of coming up heads. Suppose we express ignorance about the value of $\theta$ by assigning it a uniform distribution.
$$
\theta \sim U[0, 1]
$$

$$
f(\theta) = I_{\{0 \le \theta\le 1\}}
$$

$$
f(\theta | y = 1) =   \frac{\theta^1(1-\theta)^0I_{\{0 \le \theta\le1\}}}{\int_{-\infty}^\infty{\theta^1(1-\theta)^0I_{\{0\le \theta \le 1\}}}}
$$

$$
f(\theta | y = 1) = \frac{\theta I_{\{0\le\theta\le1\}}}{\int_0^1{\theta d\theta}} = 2\theta I_{\{0\le\theta\le1\}}
$$

Now if we didn't want to take the integral we could've done this approach
$$
f(\theta | y) \propto f(y|\theta)f(\theta) \propto \theta I_{\{0\le\theta\le1\}}
$$
Which then we need to find the constant such that it's a proper PMF. In this case, it's $2$.

Since it's a proper PMF, we can perform interval probabilities as well.  This is called Posterior interval estimates.
$$
P(0.025 < \theta < 0.975) = \int_{0.025}^{0.975}{2\theta d \theta} = (0.975)^2 - (0.025)^2 = 0.95
$$

$$
P(\theta > 0.05) = 1 - (0.05)^2 = 0.9975
$$

These are the sort of intervals we would get from the prior and asking about what their posterior probability is.

In other cases, we may want to ask, what is the posterior interval of interest? What's an interval that contains 95% of posterior probability in some meaningful way? This would be equivalent then to a frequentest confidence interval. We can do this in several different ways, 2 main ways that we make Bayesian Posterior intervals or credible intervals are equal-tailed intervals and highest posterior density intervals.

## Equal-tailed Interval

In the case of an equal-tailed interval, we put the equal amount of probability in each tail. So to make a 95% interval we'll put 0.025 in each tail. 

To be able to do this, we're going to have to figure out what the quantiles are. So we're going to need some value, $q$, so that
$$
P(\theta < q | Y = 1) = \int_0^9{2\theta d\theta} = q^2
$$

$$
P(\sqrt{0.025} < \theta < \sqrt{0.975}) = P(0.158 < \theta < 0.987) = 0.95
$$

This is an equal tailed interval in that the probability that $\theta$ is less than 0.18 is the same as the probability that $\theta$ is greater than 0.987. We can say that under the posterior, there's a 95% probability that $\theta$ is in this interval.

## Highest Posterior Density (HPD)

Here we want to ask where in the density function is it highest? Theoretically this will be the shortest possible interval that contains the given probability, in this case a 95% probability.
$$
P(\theta > \sqrt{0.05} | Y = 1) = P(\theta > 0.224 | Y = 1) = 0.95
$$
This is the shortest possible interval, that under the posterior has a probability 0.95. it's $\theta$ going from 0.224 up to 1.



The posterior distribution describes our understanding of our uncertainty combinbing our prior beliefs and the data. It does this with a probability density function, so at the end of teh day, we can make intervals and talk about probabilities of data being in the interval. 

This is different from the frequentest approach, where we get confidence intervals. But we can't say a whole lot about the actual parameter relative to the confidence interval. We can only make long run frequency statements about hypothetical intervals.

In this case, we can legitimately say that the posterior probability that $\theta$ is bigger than 0.05 is $0.9975$. We can also say that we believe there's a 95% probability that $\theta$ is in between 0.158 and 0.987.



Bayesians represent uncertainty with probabilities, so that the coin itself is a physical quantity. It may have a particular value for $\theta$.

It may be fixed, but because we don't know what that value is, we represent our uncertainty about that value with a distribution. And at the end of the day, we can represent our uncertainty, collect it with the data, and get a posterior distribution and make intuitive statements.



#### 

Frequentest confidence intervals have the interpretation that "If you were to repeat many times the process of collecting data and computing a 95% confidence interval, then on average about 95% of those intervals would contain the true parameter value; however, once you observe data and compute an interval the true value is either in the interval or it is not, but you can't tell which." 

Bayesian credible intervals have the interpretation that "Your posterior probability that the parameter is in a 95% credible interval is 95%." 
