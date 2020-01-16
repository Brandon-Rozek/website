# Lecture for March 13th

## Methods

Methods are small blocks of statements that make it easier to solve a problem. It usually focuses on solving a small part of the overall problem.

Usually in methods you provide some sort of input and get some output out of it.

### Advantages

- Code readability
- Modular program development (break up the problem in chunks)
- Incremental development
- No redundant code!

### Method definition

Consists of a method name, input and output and the block of statements.

Usually this is succinctly written using JavaDocs which is what you see in the JavaAPI

### Method Call

A method call is the execution of the method. The statements defined in the method is what will execute.

### Method Stubs

Recall from method definition the parts of the method definition. Now look at the following method

```java
String[] split(String s)
```

The output here is `String[]`

The method name is `split`

The input is `String s`

## Modular Programming

Let us look at the following example:

The program should have a list of grocery prices. It should be able to calculate the total cost of groceries. The store gives a student discount of 5%. The program should calculate this discount and update the total, it should calculate and add the 2.5% tax.

- First you should add it all up
- Then compute the discount
- Then add the tax

## Parts of a method definition

```java
public static int timesTwo(int num) {
    int two = num * 2;
    return two;
}
```

It first starts off by declaring the visibility `public`

The return type if `int`

The method name is `timesTwo`

The input parameter is `int num`

Between the curly braces is the *body* of the method

## Calling a Method

```java
int a = 5;
int b = 3;

int ans = multiply(a, b)
```

The method call is `multiply(a, b)` and the result is stored in the variable `ans`