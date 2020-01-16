# Lecture for February 8th

##Switch Statements

Another way to perform multiway branching. Comparing a variable and constant values (`String`, `int`, `char`)

Switch statements cannot be used with `boolean`, `double`, or `float`s

### Syntax

```java
switch (variable) {
  case value1:
    // Do something
    break;
  case value2:
    // Do something else
    break;
  //...
  default:
    // If all else fails do this
    break;
}
```

`case` is a reserved word that means "when our variable in consideration is equal to..."

If you forget the `break` keyword, then the program will keep doing the work of all the statements until it hits a `break` keyword.

### Example Switch Syntax

```java
switch (birthday) {
  case 1: 
    birthstone = "garnet";
    break;
  case 2:
    birthstone = "amethyst";
    break;
  // ....
  default:
    System.out.println("Not valid");
    break;
}
```

## Comparing Strings Relationally

Comparing strings are based on the ASCII value of characters

Sorting strings will result in strings being in alphabetical or reverse alphabetical order. The values of the strings are compared character by character from the left with each ASCII value.

To compare strings use the `compareTo()` method.  Here is the format of the call

```java
str1.compareTo(str2)
```

This returns a *negative number* when `str1` is less than `str2`

This returns `0` when `str1` is equal to `str1`

This returns a *positive number* when `str1` is greater than `str2`

### Example

```java
String a = "apple";
String b = "banana";

int x = a.compareTo(b); // x = -1

int y = b.compareTo(a); // y = 1
```

## Ternary Operator

With a ternary operator, you can shorten statements where a value is determined by an if statement

```java
String output = "";
if (movieRating > 4) {
  output = "Fan favorite";
} else {
  output = "Alright";
}
```

Is equivalent to

```java
String output = "";
output = (movieRating > 4)? "Fan favorite": "Alright";
```

### Another Example

```java
double shipping;
if (isPrimeMember) {
  shipping = 0;
} else {
  shipping = 3.99;
}
```

Is equivalent to

```java
double shipping = (isPrimeMember)? 0: 3.99;
```

