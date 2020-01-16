# Lecture for January 23

## Java Class

In Java, your code must live in a class.

```java
public class NameOfClass {
  public static void main(String[] args) {
    // All program code
  }
}
```

It is important that `NameOfClass` is named meaningfully for the code. It is convention to use CamelCase when using classes. (Capitalize your class names!)

All methods have a method signature, it is unique to it. For main it is the words `public static void` and the argument `String[] args`.

`public` means that any other piece of code can reference it.

`void` means that the method returns nothing

`main` is the name of the method. It is important to have `main` since that tells the Java Interpreter where to start in your program.

`String[] args` is the command line arguments inputted into the program. For this part of the class, we don't need to worry about it.

If you noticed `String` is a class, it is not a primitive type. This is denoted in Java by having it capitalized.

## Arithmetic Expressions

There is an order of operations in programming as well. It goes like this:

1. Parenthesis
2. Unary Operations
3. *, /, %
4. +, -

And from there you read from left to right.

## Constant Variables

These are variables that can never be changed

```java
final int MINUTES_PER_HOUR = 60
```

The keyword `final` indicates to the Java compiler that it is a constant variable.

By convention, constants are in all caps with underscores being separated between the words



## Java Math Library

There are some arithmetic expressions that we want to be able to do and we cannot achieve that simply with the standard operations

| Method         | Description                   |
| -------------- | ----------------------------- |
| Math.sqrt(x)   | square root                   |
| Math.abs(x)    | absolute value                |
| Math.pow(a, b) | exponentiation $a^b$          |
| Math.max(a, b) | returns the maximum of a or b |
| Math.min(a, b) | returns the minimum of a or b |
| Math.round(x)  | rounds to the nearest integer |

## Example: Finding Areas

```java
public class MoreVariables
  public static void main(String[] args) {
  	// Decrate a variable
  	int x;
  
  	// Initialize ia variable
  	x = 5;
  
  	// Area of a square
  	int squareArea = x * x;
  	System.out.println("Area of a square: " + squareArea);
  	double newSquare = Math.pow(x, 2);
  	System.out.println("Area of square: " + newSquare);
  
  	// Area of Circle
  	final double PI = 3.14159;
  	double radius = 3;
  	double circleArea = radius * radius * PI;
  	System.out.println("Area of circle: " + circleArea);
  	
}
```

