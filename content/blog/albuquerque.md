---
id: 2234
title: Albuquerque Real Estate Multiple Regression model
date: 2017-07-12T01:07:39+00:00
author: Brandon Rozek
layout: revision
guid: https://brandonrozek.com/2017/07/2227-revision-v1/
permalink: /2017/07/2227-revision-v1/
---
### Introduction

Albuquerque, New Mexico is a city of thriving culture. The population has grown drastically within the past several years and is a hotspot for New Mexico. Albuquerque’s one-of-a-kind southwestern culture is all around the city, from the quaint shops, Pueblo and Spanish inspired architecture and world famous cuisine, to the music and art of the city. Being the largest city in the state, it has a wide variety of homes across the entire city whether it be within the actual city of Albuquerque ore in the outskirts. Many people flock to the city for the weather. It is a mildly dry climate with roughly 310 days of solid sunshine each year, making it a literal hotspot for people who enjoy the outdoors and warm weather. The city has little to no natural disasters that threaten everyday life, make it a safe place to settle. In the city of Albuquerque, there is a wide variety of living communities throughout the area. As mentioned above, there are different diverse communities. The housing availability is vast as well. The housing market in this region is vast. Because there is little to no potential for natural disasters it causes the market to grow due to less of a liability for increased damage from weather. Albuquerque, has one of the lowest costs of living than anywhere else in the country which makes it a great place to invest in the housing market. The goal of this project is to figure out details of real estate, specifically in the city of Albuquerque, New Mexico. In the dataset given, the predictors available are square footage, age of home, number of features, amount in taxes, and several binary variables. Those binary variables being whether or not the home was of a custom design, is located in a corner location, or if it is located in the northeast quadrant of the city.

### Descriptive Statistics

Our dataset features a representative sample of 117 homes in Albuquerque, New Mexico. From this dataset, we can describe the key patterns that arise and build an intuition for what is to come in our inferential statistics section. It is important to build this intuition since it helps when generalizing to a population.

#### Distribution of Data

To understand the boxplot of interactions shown by Figure 1, we first need to establish what each of the indices or numbers under the x-axis represent. The first index discloses whether or not the home is located in the northeast quadrant of Albuquerque, New Mexico. The second 1index tells us whether or not the home had a custom design. And finally, the third index indicates whether or not the home is located in the corner of an intersection. From the boxplot of interactions, we can see that homes with a custom design tend to have a higher price than homes that don’t. There are no other patterns from this figure that we can readily pick up in terms of how the different combination of factors affect a home’s price. Figure 2 consists of multiple boxplots each comparing the price distribution of the different levels in all the categorical variables. From this we can reconfirm that having a custom design leads to a higher price distribution. We also see that the Northeast quadrant has a larger variation in price. There does not seem to be any significant difference in the price of homes depending on if it’s located on a corner. Finally, the more features a home has, the larger the variation in prices become. Figure 3 shows a scatterplot matrix of our data. From the matrix we can see the possibility of a linear correlation between price and square footage, as well as, price and tax. There is no evidence, however, of linear correlation between price and the age of the home. This suggests that perhaps age will not become a significant factor in our model. Figure 4 contains histograms of the different quantitative variables. As shown in the figure, the histograms are all right skewed. This shows that the majority of homes are in the lower price range while there are a few homes in the upper price region that might skew our model. Figure 5 shows the distribution of the data in terms of the categorical variables. It is interesting to note that the number of features falls in a gaussian like curve which is unimodal and symmetric at about 4 features. There are more homes that do not have a custom design and do not lie on a corner than ones that do. In this dataset, there are also more homes in the northeast quadrant than homes that are not. Figure 6 shows the distribution of taxes to be right skewed as well.

#### Effect/Interaction Plots

In the following section we will consider the effect of different categorical variables on the price of homes in Albuquerque and the other variables. The effect plots are used primarily to build an intuition on an individual variable’s effect on the price of a home. Interaction plots, however, analyze the influence of a variable on another’s effect on the price of a home. If the lines in an interaction plot intersect, it tells us that a categorical variable has a significant influence on another’s effect on the price of a home. The main effect plots in Figure 7 shows us the mean price of a home in relation to the different levels for each of the factors in the dataset. Similar to what was discovered in the boxplot figures, having a custom design increases the price of a home drastically compared to the increase of the price of a home by other factors. Having a home in a non-corner location slightly decreases the value of a home on average. Finally, it is shown in the Feature Effect plot that increases in the number of features increases the price of a home. An interesting thing to note is how in the case of 8 features, the average price of a home decreases. Figures 8, 9, and 10 show the interaction plots of different categorical variable combinations. In Figures 8 and 9, the lines do not intersect, therefore we can conclude that being in the northeast bears no influence on how custom design influences the price of the home and being in the northeast also bears no influence on how the corner location affect on the price. Figure 10, however, shows an interaction between corner location and custom design. This suggests that corner location has an influence on how custom design effects the price. 

#### Missing Data

In the dataset provided, 44% of the homes are missing some data. Missing data, like outliers, are not to be ignored. To deal with missing data, one needs to know the implications of missing data on the analysis. From there, we can think of several techniques to deal with the absence of the data. One of the most important implications to check is to see if the data is missing at random. If the data is not missing at random, then it taints the representability of the sample, making it harder to generalize to a population. In the dataset provided there are two variables that contain missing data. Figure 11 shows how 42% of the data is missing the age variable and 9% of the data is missing the Tax variable. Looking at the right side of Figure 11, we can see the pattern of missing data in our set. 35% of the data in our set is only missing the age variable, 7% of our data is missing the age and tax variable, and only 2% of our data is missing the tax variable alone. Figure 12 shows us the missing data with respect to quantitative variables such as price, square footage, and tax. As seen in the figure, the missing data is spread equally throughout the distribution. Figure 13 shows us the missing data with respect to the categorical variables in our dataset. As seen in the figure, the proportion of missing data in the binary variables are about the same for each level. When looking at the number of features, however, there is a higher proportion of data missing in the homes with fewer features than in the homes with more features. Looking at the scatterplot matrix of missing values in Figure 14, we can see that the missing values in red are spread out evenly through the observed values in blue. Missing data with respect to age was not considered since the majority of the missing data comes from the age variable.

### Inferential Statistics

Now that we’ve described the sample, we can now look forward to generalizing our suspicions to the population. In this section, we define the hypotheses of interest in our model and then consider different techniques that lead up to the final model and analysis.  
Hypotheses The main hypothesis of interest is if the model is significant.  
➢ H​ 0​ : There is no linear association between the price of homes in Albuquerque, New Mexico and any of the following: square footage, age of the home, tax, number of features, corner location, northeast location, or custom design.  
➢ H​ A​ : There is a linear association between the price of homes in Albuquerque, New Mexico and at least one of the following predictors: square footage, age of the home, tax, number of features, corner location, northeast location, or custom design. Afterwards, we consider if square footage, age, tax, number of features, corner location, northeast location, or custom design are significant predictors in the model individually. 

#### Ignore Missing Data Technique

One of the first regression models we considered is if we ignore all of the missing data. Since 44% of our data have missing values, this drops our degrees of freedom significantly to 61. This technique also doesn’t utilize all of the data, which is prefered so that it doesn’t affect the coefficients of our model. Running the stepwise algorithm to maximize the AIC, we obtain the following model  
PRICE = 97.92321 + 0.33638(SQFT) + 0.52308(TAX) + 177.18519(CUST1) − 77.82234(COR1)  
Where the p-value of the model is less than 2.2e-16. At a 5% significance level, there is a linear association between the price of the home and at least one of the following predictors: square footage, tax, custom design, or corner location. Looking at the individual t-tests for predictor significance, square footage, tax, and custom design all have a p-value around or less than 0.01 which rejects the null hypotheses of those predictors. This tells us that square footage, tax, and custom design are all significant predictors in our model. However, corner location only have a p-value of 0.09, which at a 5% significant level, fails to reject the null hypothesis. Corner location is not a significant predictor in our model. The residual standard error in this model is $155,400 which is about 15% of the mean price value of a home. The adjusted R​ 2 value is 0.8523, which means that about 85% of the variation in the prices are accounted for in the variation of the model. Not all of the conditions are met for this model and since we ignore a good chunk of the data, this model is not fully appropriate for our usage. In our next attempt, we will increase the number of observations that we include in our analysis. 

#### Remove Age Column Technique

##### Justification of Removal of Age Variable

Most of the data missing is in the age variable. Age is also not a significant predictor in the model made in the previous section, therefore, our next idea was to remove the age variable from the dataset. It is important, however, to establish that the age data is truly missing at random and removing it won’t significantly affect the analysis. We do this by removing the only other variable that has missing data (tax) from the dataset. Looking at Figures 17 and 18, it did not change significantly the distribution of missing data with respect to the different variables. This lets us comfortably remove the age column from our dataset. From here, we then repeat the Ignore Missing Data technique. This time since only 9% of the data is missing, our degrees of freedom in this analysis increases from 61 to 102. Having a greater degrees of freedom allows us to have more statistical power in our analysis. 

##### Variable Selection and Test Results

Running through the stepwise algorithm to maximize AIC, we get the following model  
PRICE = 175.16603 + 0.67707(TAX) + 156.81481(CUST1) + 0.20760(SQFT) − 83.40126(COR1)  
The p-value of this model is less than 2.2e-16, which at a 5% significance level, leads us to reject the null hypothesis and state that price has a linear association between at least one of the predictors in the model. Looking at the t-tests for predictor significance, all of the p-values are less than 0.05, which leads us to reject all the null hypotheses, and state that all of the predictors in this model: tax, custom design, square footage, and corner location are significant. The residual standard error in this model is $162,300 which is slightly higher from the $155,400 in the previous model. Though the proportion that this residual standard error is of the mean of the price set is the same at 15%. The adjusted R​ 2 value is 0.8213, which means that 82% of the variation in the prices are accounted for by the variation in the model. This dropped from the previous 85% value from the  
previous model. The residual standard error and adjusted R​ 2 values indicate that this model is worse in terms of its predictive ability. This model, however, takes more of the data into account, which makes it more accurate when considering the data as a whole and not the subsetted data that arrives from removing the null entries. In this model, we still lose about 9% of our data. In our next model, we will consider a technique that allows us to use the entire dataset. 

#### Multiple Imputation

To take the entire dataset into account we need to decide how to handle the missing values. Multiple imputation is a technique that randomly samples from the existing distribution to take place of the missing data multiple times. The benefits of multiple imputation is that it preserves the mean and variance of the data. For multiple imputation to work, the data must be missing at  
random. In the missing data section, we described how the missing data is spread equally with respect to the different variables. This allows us to say that the Missing at Random condition is met. 

##### Variable Selection and Test Results

Running the stepwise algorithm to maximize the AIC value, we get the following model  
PRICE = 138.09421 + 0.65373(TAX) + 0.23709(SQFT) + 124.31776(CUST2) − 6 7.17475(COR2)  
From the F-Test, we can reject the null hypothesis at a 5% significance level due to the fact that the p-value is less than 2.2e-16. This means that there is a linear association between price and one of the predictors: tax, square footage, custom design, and corner office. All of the T-Tests for predictor significance aside from COR2 have a p-value of less than 0.05. Meaning, we reject the appropriate null hypotheses and state that tax, square footage, and custom design are significant predictors. The residual standard error is $167,700 with 112 degrees of freedom. This value corresponds to 16% of the mean price of a home. The adjusted R​ 2 value is 0.8056, which means that about 81% of the variation in the prices is accounted for by this model. The residual standard error and adjusted R​ 2 values are again worse than the previous model. However, since this model uses the entire dataset, we can say that this is a more representative sample of the data than the previous models. To lower the amount of error in this model, we considered removing the outliers. In this model there are six outliers as shown in Figure 19. Since they are significantly far from the middle 50% of the price distribution, we removed them in the following section to better make a model that describes the main portion of the data.

#### Multiple Imputation without Outliers

Removing the outliers from the model and running the stepwise algorithm to maximize AIC, we obtain  
PRICE = 76.47917 + 0.64130(TAX) + 0.27290(SQFT) + 77.58816(CUST2)  
6For the F-Statistic, the p-value is less than 2.2e-16. At a 5% significance level, we reject the null hypothesis and state that there is a linear association between price and at least one of the following: tax, square footage, or custom design. The p-values of the T-Tests for predictor significance tells us that at a 5% significant level. all of the predictors are significant since all of the p-values are less than 0.05. The residual standard error of this model is $112,700 which is 11% of the mean of the dataset.  
The adjusted R​ 2 value is 0.8901, which means that 89% of the variation in the prices is accounted for by the variation of the model. In this model, the residual standard error is lower and the adjusted R​ 2 value is higher than the previous models. This tells us that it is a better fit for the data without the outliers. Looking at the outlier effect on the coefficients, we can see that without the outliers the term relating to the corner location goes away from the model. That then significantly changes the  
coefficients of CUST2 and the y-intercept. 

##### Checking the Conditions for Inference

Before we conclude with the analysis, we must first check the conditions for inference to see if the technique is appropriate for our data.  
<u>Independence Assumption:</u>  
A house’s selling price can depend on another’s so this condition is not met.  
<u>Randomization Condition:</u>  
The dataset is comprised of a random sample of records of resale of homes which satisfies the  
randomization condition.  
<u>Straight Enough Condition:</u>  
The scatterplot matrix in Figure 20 shows that for the predictors square footage and tax that the  
scatterplot is straight enough and doesn’t have any bends or curves.  
<u>Equal Variance Assumption:</u>  
The residual analysis in Figure 21 shows that the outliers are not spread equally on the  
scatterplot. Therefore, the equal variance assumption is not met.  
<u>Nearly Normal Condition:</u>  
The QQ-Plot in Figure 21 shows that the residuals follow a unimodal and symmetric distribution.  
Taking out the outliers in the model also did not introduce any new outliers in the boxplot.  
<u>Missing At Random Condition:</u>  
7The discussion in the descriptive statistics section about the missing data tells us that the data  
is missing evenly with respect to the different variables. Therefore, it is safe to assume that the  
data is missing at random  
<u>Multicollinearity Condition:</u>  
All of the VIF values are lower than 10, therefore this condition is met.

The conditions for inference are not fully met due to the equal variance assumption. This means that our model will be more inaccurate for some price range of homes than others. Looking at our residual analysis, it appears that the inaccuracies happen when the price of the home is higher. There weren’t many outliers in the dataset (6 out of 117 or 5%) so removing these outliers makes the model more representative to the majority of the houses in the market. Since this model is intended to be used when analyzing prices of homes in the area, it is better not to include the outliers that most people don&#8217;t intend to buy. Since the error term is unimodal and symmetric, we can be at ease that there isn’t any other confounding factor in our model. Overall, this is a good model to use for inference and prediction as long as one doesn’t use it to describe the outliers.

### Conclusion

The multiple imputation model without outliers is the best model outlined in this paper for describing the price of housing in this region. The formula is re-expressed here  
PRICE = 76.47917 + 0.64130(TAX) + 0.27290(SQFT) + 77.58816(CUST2)  
This states that for every dollar of tax spent on the home, the home increases on average by $64 given the other parameters stay constant. The same concept applies to square footage and custom design. For every square foot added to the home, the value of it increases on average by $27. Having a home with a custom design increases the value of the home by $7700. This model is more reliable the lower the price of the home is. When it comes to high cost homes, the error produced by the model increases. From this model, we conclude that property tax, square footage, and whether or not a home is built from a custom design are the most significant factors in the price of a home in Albuquerque, New Mexico.