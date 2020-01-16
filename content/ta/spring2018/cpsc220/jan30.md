# Lecture for January 30

## Random Number Generator

One of the ways you can do a random number generator is through this method:

Import a class called random 

```java
import java.util.Random;
```

Then you need to create a `Random` object

```java
Random rand = new Random();
```

After this you can call the  `nextInt()` method to get a random number between 0 and $2^{32}$

```java
int randInt = rand.nextInt();
```

If you don't want a random number between 0 and $2^{32}$ but instead to another maximum value, then you can call  the `nextInt` method inserting the max integer as a parameter.

Random Integer from 0-10 (not including 10)

```java
int randInt2 = rand.nextInt(10);
```

## Output

We have already encountered `System.out.println` and `System.out.print` but let us go over the differences again.

`System.out.println()` prints the contents inside the parenthesis and appends a newline character afterwards so that the next output is on a new line

`System.out.print()` prints the contents inside the parenthesis and does not output a newline character



### Formatting Output

If you want more control on how your output is displayed, it is recommended that you use `System.out.printf` to format your output

First, you need to specify your type using the % instruction

- d for integer
- f for decimal

Example:

```java
int sum = 50;
System.out.printf("Total = %d", sum);
```

This outputs 

```reS
Total = 50
```

Notice here that there is no concatenation required like the previous two methods, instead you insert the variables as parameters

Let us deconstruct the % instruction

% __ __ . __ __

The first underline is the + - 0 space (sometimes we want to pad the money with zeros)

The second underline is the width of the text

The third underline is the number of decimal places

The the final underline is the specifier `f` for decimal and `d` for integer

<u>Example</u>

```java
double amount = 0.5;
System.out.printf("Total Due: %0.2f")
```

This outputs

```reStructuredText
Total Due: 0.50
```

