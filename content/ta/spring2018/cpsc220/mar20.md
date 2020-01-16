# Lecture for March 20th

## Unit Testing

With unit testing you are able to test small parts as you go. With unit testing, you can test many examples and border cases (extreme inputs) to see how your code reacts to different input.

## Variable Scope

A variable declared inside a method is only accessible inside that method.

A good rule of thumb is that if a variable is declared within curly braces {} then it does not exist outside that curly brace.

## Method Overloading

Sometimes we need to have methods with the same name but different input parameters. 

```java
public static int multiply(int a, int b) {
    return a * b;
}
```

This method only works with integers, what if we want to multiply two doubles?

We can overload the method by declaring another method with the same name.

```java
public static double multiply(double a, double b) {
    return a * b;
}
```

