How do we choose a prior?

Our prior needs to represent our personal perspective, beliefs, and our uncertainties.

Theoretically, we're defining a cumulative distribution function for the parameter
$$
\begin{cases}
P(\theta \le c)  & c \in \mathbb{R}
\end{cases}
$$
This is true for an infinite number of possible sets. This isn't practical to do, and it would be very difficult to do coherently so that all the probabilities were consistent.

In practice, we work with a convenient family that's sufficiently flexible such that a member of a  family represents our beliefs.

Generally if one has enough data, the information in the data will overwhealm the information in the prior. And so, the prior is not particularly important in terms of what you get for the posterior. Any reasonable choice of prior will lead to approximately the same posterior. However, there are some things that can go wrong.

## Example of Bad Prior

Suppose we chose a prior that says the probability of $P(\theta = \frac{1}{2}) = 1$ 

And thus, the probability of $\theta$ equaling any other value is $0$. If we do this, our data won't make a difference since we only put a probability of $1$ at a single point.
$$
f(\theta|y) \propto f(y|\theta)f(\theta) = f(\theta) = \delta(\theta)
$$

In the basic context, events with prior probability of zero have a posterior probability of zero. Events with a prior probability of one, have a posterior probability of one.

Thus a good Bayesian will not assign probability of zero or one to any event that has already occurred or already known not to occur.

## Calibration

A useful concept in terms of choosing priors is that of the calibration of predictive intervals. 

If we make an interval where we're saying we predict 95% of new data points will occur in this interval. It would be good if in reality 95% of new data points actually did fall in that interval. 

How do we calibrate to reality? This is actually a frequentest concept but this is important for practical statistical purposes that our results reflect reality.

We can compute a predictive interval, this is an interval such that 95% of new observations are expected to fall into it. It's an interval for the **data** rather than an interval for $\theta$
$$
f(y) = \int{f(y|\theta)f(\theta)d\theta} = \int{f(y, \theta)d\theta}
$$
Where $f(y,\theta)$ is the joint density of Y and $\theta$.

This is the prior predictive before any data is observed.

**Side Note:** From this you can say that $f(y, \theta) = f(y|\theta)f(\theta)$

## Binomial Example

Suppose we're going to flip a coin ten times and count the number of heads we see. We're thinking about this in advance of actually doing it, so we're interested in the predictive distribution. How many heads do we predict we're going to see?
$$
X = \sum_{i = 1}^{10}{Y_i}
$$
Where $Y_i$ is each individual coin flip.

If we think that all possible coins or all possible probabilities are equally likely, then we can put a prior for $\theta$ that's flat over the interval from 0 to 1.
$$
f(\theta) = I_{\{0 \le \theta \le 1\}}
$$

$$
f(x) = \int{f(x|\theta)f(\theta)d\theta} = \int_0^1{\frac{10!}{x!(10-x)!}\theta^x(1-\theta)^{10 -x}(1)d\theta}
$$

Note that because we're interested in $X$ at the end, it's important that we distinguish between a binomial density and a Bernoulli density. Here we just care about the total count rather than the exact ordering which would be Bernoulli's

For most of the analyses we're doing, where we're interested in $\theta$ rather than x, the binomial and the Bernoulli are interchangeable because the part in here that depends on $\theta$ is the same.

To solve this integral let us recall some facts
$$
n! = \Gamma(n + 1)
$$

$$
Z \sim Beta(\alpha, \beta)
$$

$$
f(z) = \frac{\Gamma(\alpha + \beta)}{\Gamma(\alpha) \Gamma(\beta)}z^{\alpha - 1}(1-z)^{\beta - 1}
$$

Let us rewrite $f(x)$
$$
f(x) = \int_0^1{\frac{\Gamma(11)}{\Gamma(x + 1)\Gamma(11 - x)}\theta^{(x + 1)-1}(1-\theta)^{(11-x)-1}d\theta}
$$

$$
f(x) = \frac{\Gamma(11)}{\Gamma(12)}\int_0^1{\frac{\Gamma(12)}{\Gamma(x + 1)\Gamma(11 - x)}\theta^{(x + 1)-1}(1-\theta)^{(11-x)-1}d\theta}
$$

The integral above is a beta density, all integrals of valid beta densities equals to one.
$$
f(x) = \frac{\Gamma(11)}{\Gamma(12)} = \frac{10!}{11!} = \frac{1}{11}
$$
For $x \in {0, 1, 2, \dots, 10}$

Thus we see that if we start with a uniform prior, we then end up with a discrete uniform predictive density for $X$. If all possible probabilities are equally likely, then all possible $X$ outcomes are equally likely.

## Posterior Predictive Distribution

What about after we've observed data? What's our posterior predictive distribution?

Going from the previous example, let us observe after one flip that we got a head. We want to ask, what's our predictive distribution for the second flip, given we saw a head on the first flip.
$$
f(y_2|y_1) = \int{f(y_2|\theta,y_1)f(\theta|y_1)}d\theta
$$
We're going to assume that $Y_2$ is independent of $Y_1$. Therefore,
$$
f(y_2 |y_1) = \int{f(y_2|\theta)f(\theta|y_1)d\theta}
$$
Suppose we're thinking of a uniform distribution for $\theta$ and we observe the first flip is a heads. What do we predict for the second flip?

This is no longer going to be a uniform distribution like it was before, because we have some data. We're going to think it's more likely that we're going to get a second head. We think this because since we observed a head $\theta$ is now likely to be at least $\frac{1}{2}$ possibly larger. 
$$
f(y_2 | Y_1 = 1) = \int_0^1{\theta^{y_2}(1-\theta)^{1-y_2}2\theta d\theta}
$$

$$
f(y_2|Y_1 = 1) = \int_0^1{2\theta^{y_2 + 1}(1-\theta)^{1-y_2}d\theta}
$$

We could work this out in a more general form, but in this case, $Y_2$ has to take the value $0$ or $1$. The next flip is either going to be heads or tails so it's easier to just plop in a particular example.
$$
P(Y_2 = 1|Y_1 = 1) = \int_0^1{2\theta^2d\theta} = \frac{2}{3}
$$

$$
P(Y_2 = 0 | Y_1 = 1) = 1 - P(Y_2 = 1 | Y_1 = 1) = 1 - \frac{2}{3} = \frac{1}{3}
$$

We can see here that the posterior is a combination of the information in the prior and the information in the data. In this case, our prior is like having two data points, one head and one tail. 

Saying we have a uniform prior for $\theta$ is equivalent in an information sense as saying we have observed one head and one tail.

So then when we observe one head, it's like we now have seen two heads and one tail. So our predictive distribution for the second flip says if we have two heads and one tail, then we have a $\frac{2}{3}$ probability of getting another head and a $\frac{1}{3}$ probability of getting another tail.

## Binomial Likelihood with Uniform Prior

Likelihood of y given theta is
$$
f(y|\theta) = \theta^{\sum{y_i}}(1-\theta)^{n - \sum{y_i}}
$$

Our prior for theta is just a uniform distribution
$$
f(\theta) = I_{\{0 \le \theta \le 1\}}
$$
Thus our posterior for $\theta$ is
$$
f(\theta | y) = \frac{f(y|\theta)f(\theta)}{\int{f(y|\theta)f(\theta)d\theta}} = \frac{\theta^{\sum{y_i}}(1-\theta)^{n - \sum{y_i}}  I_{\{0 \le \theta \le 1\}}}{\int_0^1{\theta^{\sum{y_i}}(1-\theta)^{n - \sum{y_i}}  I_{\{0 \le \theta \le 1\}}d\theta}}
$$
Recalling the form of the beta distribution we can rewrite our posterior as
$$
f(\theta | y) = \frac{\theta^{\sum{y_i}}(1-\theta)^{n - \sum{y_i}}  I_{\{0 \le \theta \le 1\}}}{\frac{\Gamma(\sum{y_i} + 1)\Gamma(n - \sum{y_i} + 1)}{\Gamma(n + 2)}\int_0^1{\frac{\Gamma(n + 2)}{\Gamma(\sum{y_i} + 1)\Gamma(n - \sum{y_i} + 1)}\theta^{\sum{y_i}}(1-\theta)^{n - \sum{y_i}}d\theta}}
$$
Since the beta density integrates to $1$, we can simplify this as
$$
f(\theta | y) = \frac{\Gamma(n + 2)}{\Gamma(\sum{y_i}+ 1)\Gamma(n - \sum{y_i}+ 1)}\theta^{\sum{y_i}}(1-\theta)^{n-\sum{y_i}}I_{\{0 \le \theta \le 1\}}
$$
From here we can see that the posterior follows a beta distribution
$$
\theta | y \sim Beta(\sum{y_i} + 1, n - \sum{y_i} + 1)
$$

## Conjugate Priors

The uniform distribution is $Beta(1, 1)$ 

Any beta distribution is conjugate for the Bernoulli distribution. Any beta prior will give a beta posterior.
$$
f(\theta) = \frac{\Gamma(\alpha + \beta)}{\Gamma(\alpha)\Gamma(\beta)}\theta^{\alpha - 1}(1-\theta)^{\beta -1}I_{\{0 \le \theta \le 1\}}
$$

$$
f(\theta | y) \propto f(y|\theta)f(\theta) = \theta^{\sum{y_i}}(1-\theta)^{n - \sum{y_i}}\frac{\Gamma(\alpha + \beta)}{\Gamma(\alpha)\Gamma(\beta)}\theta^{\alpha - 1}(1 - \theta)^{\beta - 1}I_{\{0 \le \theta \le 1\}}
$$

$$
f(y|\theta)f(\theta) \propto \theta^{\alpha + \sum{y_i}-1}(1-\theta)^{\beta + n - \sum{y_i} - 1}
$$

Thus we see that this is a beta distribution
$$
\theta | y \sim Beta(\alpha + \sum{y_i}, \beta + n - \sum{y_i})
$$
When $\alpha$ and $\beta$ is one like in the uniform distribution, then we get the same result as earlier.



This whole process where we choose a particular form of prior that works with a likelihood is called using a conjugate family.

A family of distributions is referred to as conjugate if when you use a member of that family as a prior, you get another member of that family as your posterior.

The beta distribution is conjugate for the Bernoulli distribution. It's also conjugate for the binomial distribution. The only difference in the binomial likelihood is that there is a combinatoric term. Since that does not depend on $\theta$, we get the same posterior.

We often use conjugate priors because they make life much more simpler, sticking to conjugate families allows us to get closed form solutions easily.

If the family is flexible enough, then you can find a member of that family that closely represents your beliefs.

## Posterior Mean and Effect Size

Returning to the beta posterior model it is clear how both the prior and the data contribute to the posterior.

We can say that the effect size of the prior is $\alpha + \beta$

Recall that the expected value or mean of a beta distribution is $\frac{\alpha}{\alpha + \beta}$

Therefore we can derive the posterior mean as
$$
posterior_{mean} = \frac{\alpha + \sum{y_i}}{\alpha + \sum{y_i}+\beta + n - \sum{y_i}}= \frac{\alpha+\sum{y_i}}{\alpha + \beta + n}
$$
We can further decompose this as
$$
posterior_{mean} = \frac{\alpha + \beta}{\alpha + \beta + n}\frac{\alpha}{\alpha + \beta} + \frac{n}{\alpha + \beta + n}\frac{\sum{y_i}}{n}
$$
We can describe this as the (prior weight * prior mean) + (data weight * data mean)

The posterior mean is a weighted average of the prior mean and the data mean.

This effective sample size gives you an idea of how much data you would need to make sure that your prior doesn't have much influence on your posterior.

If $\alpha + \beta$ is small compared to $n$ then the posterior will largely just be driven by the data. If $\alpha + \beta$ is large relative to $n$ then the posterior will be largely driven by the prior.

We can make a 95% credible interval using our posterior distribution for $\theta$. We can find an interval that actually has 95% probability of containing $\theta$.

Using Bayesian Statistics we can chain together dong a sequential update every time we get new data. We can get a new posterior, and we just use our previous posterior as a prior to do another update using Baye's theorem.

## Data Analysis Example in R

Suppose we're giving two students a multiple-choice exam with 40 questions, where each question has four choices. We don't know how much the students have studied for this exam, but we think that they'll do better than just guessing randomly

1) What are the parameters of interest?

The parameters of interests are $\theta_1 = true$ the probability that the first student will answer a question correctly, $\theta_2 = true$ the probability that the second student will answer a question correctly.

2) What is our likelihood?

The likelihood is $Binomial(40, \theta)$, if we assume that each question is independent and that the probability a student gets each question right is the same for all questions for that student.

3) What prior should we use?

The conjugate prior is a beta prior. We can plot the density with `dbeta`

```R
theta = seq(from = 0, to = 1, by = 0.1)
# Uniform
plot(theta, dbeta(theta, 1, 1), type = 'l')
# Prior mean 2/3
plot(theta, dbeta(theta, 4, 2), type = 'l')
# Prior mean 2/3 but higher effect size (more concentrated at mean)
plot(theta, dbeta(theta, 8, 4), type = 'l')
```

4 ) What are the prior probabilities $P(\theta > 0.25)$? $P(\theta > 0.5)$? $P(\theta > 0.8)$?

```R
1 - pbeta(0.25, 8, 4)
#[1] 0.998117
1 - pbeta(0.5, 8, 4)
#[1] 0.8867188
1 - pbeta(0.8, 8, 4)
#[1] 0.16113392
```



5) Suppose the first student gets 33 questions right. What is the posterior distribution for $\theta_1$?  $P(\theta > 0.25)$? $P(\theta > 0.5)$? $P(\theta > 0.8)$? What is the 95% posterior credible interval for $\theta_1$?
$$
Posterior \sim Beta(8 + 33, 4 + 40 - 33) = Beta(41, 11)
$$
With a posterior mean of $\frac{41}{41+11} = \frac{41}{52}$

We can plot the posterior distribution with the prior

```R
plot(theta, dbeta(theta, 41, 11), type = 'l')
lines(theta, dbeta(theta, 8 ,4), lty = 2) #Dashed line for prior
```

Posterior probabilities

```R
1 - pbeta(0.25, 41, 11)
#[1] 1
1 - pbeta(0.5, 41, 11)
#[1] 0.9999926
1 - pbeta(0.8, 41, 11)
#[1] 0.4444044
```

Equal tailed 95% credible interval

```R
qbeta(0.025, 41, 11)
#[1] 0.6688426
qbeta(0.975, 41, 11)
#[1] 0.8871094
```

95% confidence that $\theta_1$ is between 0.67 and 0.89



6) Suppose the second student gets 24 questions right. What is the posterior distribution for $\theta_2$?  $P(\theta > 0.25)$? $P(\theta > 0.5)$? $P(\theta > 0.8)$? What is the 95% posterior credible interval for $\theta_2$
$$
Posterior \sim Beta(8 + 24, 4 + 40 - 24) = Beta(32, 20)
$$
With a posterior mean of $\frac{32}{32+20} = \frac{32}{52}$

We can plot the posterior distribution with the prior

```R
plot(theta, dbeta(theta, 32, 20), type = 'l')
lines(theta, dbeta(theta, 8 ,4), lty = 2) #Dashed line for prior
```

Posterior probabilities

```R
1 - pbeta(0.25, 32, 20)
#[1] 1
1 - pbeta(0.5, 32, 20)
#[1] 0.9540427
1 - pbeta(0.8, 32, 20)
#[1] 0.00124819
```

Equal tailed 95% credible interval

```R
qbeta(0.025, 32, 20)
#[1] 0.4808022
qbeta(0.975, 32, 20)
#[1] 0.7415564
```

95% confidence that $\theta_1$ is between 0.48 and 0.74



7) What is the posterior probability that $\theta_1 > \theta_2$? i.e., that the first student has a better chance of getting a question right than the second student?

Estimate by simulation: draw 1,000 samples from each and see how often we observe $\theta_1 > \theta_2$

```R
theta1 = rbeta(100000, 41, 11)
theta2 = rbeta(100000, 32, 20)
mean(theta1 > theta2)
#[1] 0.975
```

## Poisson Data (Chocolate Chip Cookie Example)

In mass produced chocolate chip cookies, they make a large amount of dough. They mix in a large number of chips, mix it up really well and then chunk out individual cookies. In this process, the number of chips per cookie approximately follow a Poisson distribution.

If we were to assume that chips have no volume, then this would be exactly a Poisson process and follow exactly a Poisson distribution. In practice, however, chips aren't that big so they follow approximately a Poisson distribution for the number of chips per cookie.
$$
Y_i \sim Poisson(\lambda)
$$

$$
f(y|\lambda) = \frac{\lambda^{\sum{y_i}}e^{-n\lambda}}{\prod_{i = 1}^n{y_i!}}
$$

This is for $\lambda > 0$

What type of prior should we put on $\lambda$? It would be convenient if we could put a conjugate prior. What distribution looks like lambda raised to a power and e raised to a negative power?

For this, we're going to use a Gamma prior.
$$
\lambda \sim \Gamma(\alpha, \beta)
$$

$$
f(\lambda) = \frac{\beta^\alpha}{\Gamma(\alpha)}\lambda^{\alpha - 1}e^{-\beta\lambda}
$$

$$
f(\lambda | y) \propto f(y|\lambda)f(\lambda) \propto \lambda^{\sum{y_i}}e^{-n\lambda}\lambda^{\alpha - 1}e^{-\beta \lambda}
$$

$$
f(\lambda | y) \propto \lambda^{\alpha + \sum{y_i} - 1}e^{-(\beta + n)\lambda}
$$

Thus we can see that the posterior is a Gamma Distribution
$$
\lambda|y \sim \Gamma(\alpha + \sum{y_i}, \beta + n)
$$
The mean of Gamma under this parameterization is $\frac{\alpha}{\beta}$

The posterior mean is going to be
$$
posterior_{mean} = \frac{\alpha + \sum{y_i}}{\beta + n} = \frac{\beta}{\beta + n}\frac{\alpha}{\beta} + \frac{n}{\beta + n}\frac{\sum{y_i}}{n}
$$
As you can see here the posterior mean of the Gamma distribution is also the weighted average of the prior mean and the data mean.

Let us present two strategies on how to choose our hyper parameters $\alpha$ and $\beta$

1. Think about the prior mean. For example, what do you think the number of chips per cookie on average is?

After this, we need some other piece of knowledge to pin point both parameters. Here are some options.

- What is your error on the number of chips per cookie? In other words, what do you think the standard deviation. Under the Gamma prior the standard deviation is $\frac{\sqrt{\alpha}}{\beta}$
- What is the effective sample size $\beta$? How many units of information do you think we have in our prior versus our data points.

2. In Bayesian Statistics, a vague prior refers to one that's relatively flat across much of the space. For a Gamma prior we can choose $\Gamma(\epsilon, \epsilon)$ where $\epsilon$ is small and strictly positive.

This would create a distribution with a mean of 1 and a huge standard deviation across the whole space. Hence the posterior will be largely driven by the data and very little by the prior.