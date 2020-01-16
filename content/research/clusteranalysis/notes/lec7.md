# Divisive Methods Pt.1

Divisive methods work in the opposite direction of agglomerative methods. They take one large cluster and successively splits it.

This is computationally demanding if all $2^{k - 1} - 1$ possible divisions into two sub-clusters of a cluster of $k$ objects are considered at each stage.

While less common than Agglomerative methods, divisive methods have the advantage that most users are interested in the main structure in their data, and this is revealed from the outset of a divisive method.

## Monothetic Divisive Methods

For data consisting of $p$ **binary variables**, there is a computationally efficient method known as *monothetic divisive methods* available.

Monothetic divisions divide clusters according to the presence or absence of each of the $p$ variables, so that at each stage, clusters contain members with certain attributes that are either all present or all absent.

The term 'monothetic' refers to the use of a single variable on which to base the split on. *Polythetic* methods use all the variables at each stage.

### Choosing the Variable to Split On

The choice of the variable on which a split is made depends on optimizing a criterion reflecting either cluster homogeneity or association with other variables.

This tends to minimize the number of splits that have to be made.

An example of an homogeneity criterion is the information content $C$

This is defined with $p$ variables and $n$ objections where $f_k$ is the number of individuals with the $k$ attribute
$$
C = pn\log{n}-\sum_{k = 1}^p{(f_k\log{f_k} - (n-f_k)\log{(n-f_k)})}
$$

### Association with other variables

Recall that another way to split is based on the association with other variables. The attribute used at each step can be chosen according to its overall association with all attributes remaining at each step.

This is sometimes termed *association analysis*.

|      | V1   | V2   |
| ---- | ---- | ---- |
|      | 1    | 0    |
| 1    | a    | b    |
| 0    | c    | d    |

####Common measures of association

$$
|ad-bc| \tag{4.6}
$$

$$
(ad-bc)^2 \tag{4.7}
$$

$$
\frac{(ad-bc)^2n}{(a+b)(a+c)(b+d)(c+d)} \tag{4.8}
$$

$$
\sqrt{\frac{(ad-bc)^2n}{(a+b)(a+c)(b+d)(c+d)}} \tag{4.9}
$$

$$
\frac{(ad-bc)^2}{(a+b)(a+c)(b+d)(c+d)} \tag{4.10}
$$

$(4.6)$ and $(4.7)$ have the advantage that there is no danger of computational problems if any marginal totals are near zero.

The last three, $(4.8)$, $(4.9)$, $(4.10)$, are all related to the $\chi^2$ statistic, its square root, and the Pearson correlation coefficient respectively.

### Advantages/Disadvantages of Monothetic Methods

Appealing features of monothetic divisive methods are the easy classification of new members and the including of cases with missing values.

A further advantage of monothetic divisive methods is that it is obvious which variables produce the split at any stage of the process.

A disadvantage with these methods is that the possession of a particular attribute which is either rare or rarely found in combination with others may take an individual down a different path.