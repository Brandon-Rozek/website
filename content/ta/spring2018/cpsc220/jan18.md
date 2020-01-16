# Lecture for January 18

## Variables and Assignment

Think about variables as buckets that hold information. Once the bucket is created, only one type of item can go in the bucket.

```java
sand bucket1;
```

We can say that bucket1 is of type `sand`, that means the only thing that can go in the bucket is sand.

```java
int bucket1;
double bucket2;
```

From the two lines above, we have *declared* the variable.

Variables store state, they are a name for a location in memory. 

Always remember to initialize your variables. Otherwise there's nothing in the bucket!

```java
bucket1 = 5;
```

 You can combine both the declaration and initialization

```java
int count = 15;
```

Remember when dealing with variables to stay true with the type, don't mix a bucket of water with a bucket of sand.

We can update `count` to contain a true value

```java
count = 55;
```

`count` no longer has the value of `15` in it. There's no record of it! It has been overwritten with the value `55`

### Primitive Types

There are 8 primitive types in Java

- boolean
- char
- byte
- short
- int
- long
- float
- double

byte through double are all *numeric* types

#### Boolean

`boolean` can only be equal to `true` or `false`

```java
boolean student = true;
```

#### Char

Stores a single character from the Unicode set

There are 16 bits per character which adds up to 65,536 characters

ASCII is the US subset of the characters. You can look this up online when needing to deal with ASCII values

```java
char firstLetter = 'A';
```

### Numeric types

The different numeric types determine the precision of your number. Since numbers are not represented the same in the computer as they are in real life, there are some approximations.

The default type you can use your code is `int` for integers and `double` for numbers with a decimal point

There are certain types of operations you can perform on numeric type

| Symbol | Meaning         | Example    | Value |
| ------ | --------------- | ---------- | ----- |
| +      | addition        | 43 + 8     | 51    |
| -      | subtraction     | 43.0-8.0   | 35.0  |
| *      | multiplication  | 43 * 8     | 344   |
| /      | division        | 43.0 / 8.0 | 5.375 |
| %      | remainder / mod | 43 % 8     | 3     |
| -      | unary minus     | -43        | -43   |

#### Increment/ Decrement

There are two types of in/decrementers postfix and prefix

Postfix:

```java
int x = 0;
int y = 7;
x++; // Shortcut for x = x + 1
y--; // Shortcut for y = y - 1
```

Prefix

```java
int x = 0, y = 7, z;
z = y * x++; // Equivalent to (y * x) + 1 = 7 * 0
z = y * ++x; // Equivalent to y * (x + 1) = 7 * 1
```

### Data Conversion

There are two types of data conversion, implicit and explicit

The compiler can perform implicit data conversion automatically.

Performing an explicit data conversion requires additional work on the programmer's part

A conversion is implicit if you do **not** lose any information in it

```java
double price = 6.99;
int sale = 3;
double total = price - sale;
```

A *cast* is an explicit data conversion. This is requested by a programmer, this can lead to loss of information

```java
int nextChar = 'b';
Character.isAlphabetic( (char) nextChar); // Let's you print the actual letter 'b' instead of the number corresponding to it

float price = 6.99;
int cost = (int) price; // cost is now 6
```

### Printing variables

You can print the values of variables using `System.out.println` and `System.out.print`

The difference is that `System.out.println` adds a new line at the end. Meaning the next print out will be on the next line.

```java
int cost = 5;
double sale = .30;
System.out.print(cost);
System.out.print(sale);
// Prints out '5.30`
System.out.println(cost);
System.out.println(sale);
// Prints out '5'
// Prints out '0.30'
```

To add a space between two variables in a print, add `" "` to the expression in between the two variables

```java
System.out.println("The total cost is " + 5 " dollars and" + " " + 93 + " cents");
// The total cost is 5 dollars and 94 cents
```

### Input from User

You can get import from the user, we can do this using the `Scanner` class.

First import it  at the top of your file

```java
import java.util.Scanner;
```

All you can do with `Scanner` is outlined in the Java API at this link https://docs.oracle.com/javase/8/docs/api/index.html?java/util/Scanner.html

Create a Scanner object

```java
Scanner input = new Scanner(System.in);
System.out.print("Please enter an integer: ");
price = input.nextInt(); // The integer that the user inputs is now stored in price
System.out.println("Your input: " + price);
```

