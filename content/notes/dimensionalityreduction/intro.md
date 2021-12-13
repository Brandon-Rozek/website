---
title: Introduction to Dimensionality Reduction
---

## Motivations

We all have problems to solve, but the data we might have at our disposal is too sparse or has too many features that it makes it computationally difficult or maybe even impossible to solve the problem.

### Types of Problems

**Prediction**: This is taking some input and trying to predict an output of it. An example includes having a bunch of labeled pictures of people and having the computer predict who is in the next picture taken. (Face or Object Recognition)

**Structure Discovery**: Find an alternative representation of the data. Usually used to find groups or alternate visualizations

**Density Estimation**: Finding the best model that describes the data. An example includes explaining the price of a home depending on several factors. 

## Advantages

- Reduces the storage space of data (possibly removing noise in the process!)
- Decreases complexity making algorithms run faster
- Removes multi-collinearity which in turn likely improves the performance of a given machine learning model
  - Multi-collinearity usually indicates that multiple variables are correlated with each other. Most models make use of independent features to simplify computations. Therefore, ensuring independent features is important.
- Data becomes easier to visualize as it can be projected into 2D/3D space
- Lessens the chance of models *overfitting*
  - This typically happens when you have less observations compared to variables (also known as sparse data)
  - Overfitting leads to a model being able to have high accuracy on the test set, but generalize poorly to reality.
- Curse of dimensionality does not apply in resulting dataset
  - Curse of dimensionality is that in high dimensional spaces, all points become equidistant

## Disadvantages

Data is lost through this method, potentially resulting in possibly insightful information being removed. Features from dimensionality reduction are typically harder to interpret leading to more confusing models.