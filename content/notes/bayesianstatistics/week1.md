# Bayesian Statistics

## Rules of Probability

Probabilities must be between zero and one, i.e., $0≤P(A)≤1$ for any event A.

Probabilities add to one, i.e., $\sum{P(X_i)} = 1$

The complement of an event, $A^c$, denotes that the event did not happen. Since probabilities must add to one, $P(A^c) = 1 - P(A)$

If A and B are two events, the probability that A or B happens (this is an inclusive or) is the probability of the union of the events:
$$
P(A \cup B) = P(A) + P(B) - P(A\cap B)
$$
where $\cup$ represents union ("or") and $\cap$ represents intersection ("and"). If a set of events $A_i$ are mutually exclusive (only one event may happen), then
$$
P(\cup_{i=1}^n{A_i}) = \sum_{i=1}^n{P(A_i)}
$$

## Odds

The odds for event A, denoted $\mathcal{O}(A)$ is defined as $\mathcal{O}(A) = P(A)/P(A^c)$ 

This is the probability for divided by probability against the event

From odds, we can also compute back probabilities
$$
\frac{P(A)}{P(A^c)} = \mathcal{O}(A)
$$

$$
\frac{P(A)}{1-P(A)} = \mathcal{O}(A)
$$

$$
\frac{1 -P(A)}{P(A)} = \frac{1}{\mathcal{O}(A)}
$$

$$
\frac{1}{P(A)} - 1 = \frac{1}{\mathcal{O}(A)}
$$

$$
\frac{1}{P(A)} = \frac{1}{\mathcal{O}(A)} + 1
$$

$$
\frac{1}{P(A)} = \frac{1 + \mathcal{O}(A)}{\mathcal{O}(A)}
$$

$$
P(A) = \frac{\mathcal{O}(A)}{1 + \mathcal{O}(A)}
$$

## Expectation

The expected value of a random variable X is a weighted average of values X can take, with weights given by the probabilities of those values.
$$
E(X) = \sum_{i=1}^n{x_i * P(X=x_i)}
$$

## Frameworks of probability

Classical -- Outcomes that are equally likely have equal probabilities

Frequentist -- In an infinite sequence of events, what is the relative frequency

Bayesian -- Personal perspective (your own measure of uncertainty)

In betting, one must make sure that all the rules of probability are followed. That the events are "coherent", otherwise one might construct a series of bets where you're guaranteed to lose money. This is referred to as a Dutch book.

## Conditional probability

$$
P(A|B) = \frac{P(A\cup B)}{P(B)}
$$

Where $A|B$ denotes "A given B"

Example from lecture:

Suppose there are 30 students, 9 of which are female. From the 30 students, 12 are computer science majors. 4 of those 12 computer science majors are female
$$
P(Female) = \frac{9}{30} = \frac{3}{10}
$$

$$
P(CS) = \frac{12}{30} = \frac{2}{5}
$$

$$
P(F\cap CS) = \frac{4}{30} = \frac{2}{15}
$$

$$
P(F|CS) = \frac{P(F \cap CS)}{P(CS)} = \frac{2/15}{2/5} = \frac{1}{3}
$$

An intuitive way to think about a conditional probability is that we're looking at a subsegment of the original population, and asking a probability question within that segment
$$
P(F|CS^c) = \frac{P(F\cap CS^c)}{PS(CS^c)} = \frac{5/30}{18/30} = \frac{5}{18}
$$
The concept of independence is when one event does not depend on another.
$$
P(A|B) = P(A)
$$
It doesn't matter that B occurred.

If two events are independent then the following is true
$$
P(A\cap B) = P(A)P(B)
$$
This can be derived from the conditional probability equation.

## Conditional Probabilities in terms of other conditional

Suppose we don't know what $P(A|B)$ is but we do know what $P(B|A)$ is. We can then rewrite $P(A|B)$ in terms of $P(B|A)$
$$
P(A|B) = \frac{P(B|A)P(A)}{P(B|A)P(A) + P(B|A^c)P(A^c)}
$$
Let's look at an example of an early test for HIV antibodies known as the ELISA test.
$$
P(+ | HIV) = 0.977
$$

$$
P(- | NO\_HIV) = 0.926
$$

As you can see over 90% of the time, this test was accurate.

The probability of someone in North America having this disease was $P(HIV) = .0026$

Now let's consider the following problem: the probability of having the disease given that they tested positive $P(HIV | +)$
$$
P(HIV|+) = \frac{P(+|HIV)P(HIV)}{P(+|HIV)P(HIV) + P(+|NO\_HIV){P(NO\_HIV)}}
$$

$$
P(HIV|+) = \frac{(.977)(.0026)}{(.977)(.0026) + (1-.977)(1-.0026)}
$$

$$
P(HIV|+) = 0.033
$$

This example looked at Bayes Theorem for the two event case. We can generalize it to n events through the following formula
$$
P(A|B) = \frac{P(B|A_1){(A_1)}}{\sum_{i=1}^{n}{P(B|A_i)}P(A_i)}
$$



## Bernoulli Distribution

~ means 'is distributed as'

We'll be first studying the Bernoulli Distribution. This is when your event has two outcomes, which is commonly referred to as a success outcome and a failure outcome. The probability of success is $p$ which means the probability of failure is $(1-p)$
$$
X \sim B(p)
$$

$$
P(X = 1) = p
$$

$$
P(X = 0) = 1-p
$$

The probability of a random variable $X$ taking some value $x$ given $p$ is
$$
f(X = x | p) = f(x|p) = p^x(1-p)^{1 - x}I
$$
Where $I$ is the Heavenside function

Recall the expected value
$$
E(X) = \sum_{x_i}{x_iP(X=x_i)} = (1)p + (0)(1-p) = p
$$
We can also define the variance of Bernoulli
$$
Var(X) = p(1-p)
$$

## Binomial Distribution

The binomial distribution is the sum of n *independent* Bernoulli trials
$$
X \sim Bin(n, p)
$$

$$
P(X=x|p) = f(x|p) =  {n \choose x} p^x (1-p)^{n-x}
$$

$n\choose x$ is the combinatoric term which is defined as
$$
{n \choose x} = \frac{n!}{x! (n - x)!}
$$

$$
E(X) = np
$$

$$
Var(X) = np(1-p)
$$

## Uniform distribution

Let's say X is uniformally distributed
$$
X \sim U[0,1]
$$

$$
f(x) = \left\{
     \begin{array}{lr}
       1 & : x \in  [0,1]\\
       0 & : otherwise
     \end{array}
   \right.
$$

$$
P(0 < x < \frac{1}{2}) = \int_0^\frac{1}{2}{f(x)dx} = \int_0^\frac{1}{2}{dx} = \frac{1}{2}
$$

$$
P(0 \leq x \leq \frac{1}{2}) = \int_0^\frac{1}{2}{f(x)dx} = \int_0^\frac{1}{2}{dx} = \frac{1}{2}
$$

$$
P(x = \frac{1}{2}) = 0
$$

## Rules of probability density functions

$$
\int_{-\infty}^\infty{f(x)dx} = 1
$$

$$
f(x) \ge 0
$$

$$
E(X) = \int_{-\infty}^\infty{xf(x)dx}
$$

$$
E(g(X))  = \int{g(x)f(x)dx}
$$

$$
E(aX) = aE(X)
$$

$$
E(X + Y) = E(X) + E(Y)
$$

If X & Y are independent
$$
E(XY) = E(X)E(Y)
$$

## Exponential Distribution

$$
X \sim Exp(\lambda)
$$

Where $\lambda$ is the average unit between observations
$$
f(x|\lambda) = \lambda e^{-\lambda x}
$$

$$
E(X) = \frac{1}{\lambda}
$$

$$
Var(X) = \frac{1}{\lambda^2}
$$

## Uniform (Continuous) Distribution

$$
X \sim [\theta_1, \theta_2]
$$

$$
f(x|\theta_1,\theta_2) = \frac{1}{\theta_2 - \theta_1}I_{\theta_1 \le x \le \theta_2}
$$

## Normal Distribution

$$
X \sim N(\mu, \sigma^2)
$$

$$
f(x|\mu,\sigma^2) = \frac{1}{\sqrt{2\pi \sigma^2}}e^{-\frac{1}{2\sigma^2}(x-\mu)^2}
$$

$$
E(X) = \mu
$$

$$
Var(X) = \sigma^2
$$

## Variance

Variance is the squared distance from the mean
$$
Var(X) = \int_{-\infty}^\infty {(x - \mu)^2f(x)dx}
$$

## Geometric Distribution (Discrete)

The geometric distribution is the number of trails needed to get the first success, i.e, the number of Bernoulli events until a success is observed.
$$
X \sim Geo(p)
$$

$$
P(X = x|p) = p(1-p)^{x-1}
$$

$$
E(X) = \frac{1}{p}
$$

## Multinomial Distribution (Discrete)

Multinomial is like a binomial when there are more than two possible outcomes.

 
$$
f(x_1,...,x_k|p_1,...,p_k) = \frac{n!}{x_1! ... x_k!}p_1^{x_1}...p_k^{x_k}
$$

## Poisson Distribution (Discrete)

The Poisson distribution is used for counts. The parameter $\lambda > 0$ is the rate at which we expect to observe the thing we are counting.
$$
X \sim Pois(\lambda)
$$

$$
P(X=x|\lambda) = \frac{\lambda^xe^{-\lambda}}{x!}
$$

$$
E(X) = \lambda
$$

$$
Var(X) = \lambda
$$

## Gamma Distribution (Continuous)

If $X_1, X_2, ..., X_n$ are independent and identically distributed Exponentials,waiting time between success events, then the total waiting time for all $n$ events to occur will follow a gamma distribution with shape parameter $\alpha = n$ and rate parameter $\beta = \lambda$
$$
Y \sim Gamma(\alpha, \beta)
$$

$$
f(y|\alpha,\beta) = \frac{\beta^n}{\Gamma(\alpha)}y^{n-1}e^{-\beta y}I_{y\ge0}(y)
$$

$$
E(Y) = \frac{\alpha}{\beta}
$$

$$
Var(Y) = \frac{\alpha}{\beta^2}
$$

Where $\Gamma(x)$ is the gamma function. The exponential distribution is a special case of the gamma distribution with $\alpha = 1$. As $\alpha$ increases, the gamma distribution more closely resembles the normal distribution.

## Beta Distribution (Continuous)

The beta distribution is used for random variables which take on values between 0 and 1. For this reason, the beta distribution is commonly used to model probabilities.
$$
X \sim Beta(\alpha, \beta)
$$

$$
f(x|\alpha,\beta) = \frac{\Gamma(\alpha + \beta)}{\Gamma(\alpha)\Gamma(\beta)}x^{n -1}(1 - x)^{\beta - 1}I_{\{0 < x < 1\}}
$$

$$
E(X) = \frac{\alpha}{\alpha + \beta}
$$

$$
Var(X) = \frac{\alpha\beta}{(\alpha + \beta)^2(\alpha+\beta+1)}
$$

The standard uniform distribution is a special case of the beta distribution with $\alpha = \beta = 1$

## Bayes Theorem for continuous distribution

$$
f(\theta|y) = \frac{f(y|\theta)f(\theta)}{\int{f(y|\theta)f(\theta)d\theta}}
$$

