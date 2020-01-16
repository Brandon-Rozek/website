# Lecture for February 27th

## Review for midterm

Chapter 1 -- Code Style, API

Chapter 2 -- Variables & Assignments, strings

Chapter 3 -- input & output

Chapter 4 -- branches (if, if/else, switch)

Chapter 5 -- loops (while, for), scope

Chapter 6 -- File Reading and Writing

## Separated vs Connected Branches

What is the output of this code?

```java
String preferredLanguage = "Spanish";
if (preferredLanguage.equals("Chinese")) {
    System.out.println("Ni hao!");
}
if (preferredLanguage.equals("Spanish")) {
    System.out.println("Hola!");
}
if (preferredLanguage.equals("French")) {
    System.out.println("Bonjour!");
}
if (preferredLanguage.equals("German")) {
    System.out.println("Gutentag!")
} else {
    System.out.println("Hello!")
}
```

The output is

```reStructuredText
Hola!
Hello!
```

This is because each of the if statements are independent from each other. Whether or not the if statement gets check is not affected by the if statements around it.

Since the preferred language equals Spanish it outputs `Hola!` But since the language is also *not German* it prints out `Hello!` as well.



## Using an Array

Square brackets notation is used to access elements, array slots can be used as variables

```java
int[] array = new int[7]; // Creates an integer array of size 7
array[0] = 5;
```



## Swapping Elements

You can swap `x` and `y` in the following way with a *temporary* variable

```java
int x = 6;
int y = 1;

int temp = x;

x = y;
y = temp;
```



## Two-Dimensional Arrays

```java
// Creates a 2D array of two rows and three columns
int[][] a = new int[2][3]
```

You can access an element of this 2D array using the conventional square bracket notation

```java
a[0][0] = 5;
```

