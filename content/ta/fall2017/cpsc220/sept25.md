# Lecture in CPSC 220 Sept 25 2017

## Constants

Adding the keyword `final` in front of a variable declaration makes the variable constant. Meaning you cannot later change it in the code.

```java
final int MAX = 10;
```

By industry norm, the style of the variable is to have it in all caps.

You CANNOT do the following

```java
final int MAX = 10;
MAX = 15;
```



## Using Libraries

1. Import the library
2. Find the method that is appropriate
3. Use it

Example:

```java
import java.util.Math;
public class MathTest {
    public static void main(String[] args) {
        double answer = Math.ceil(5.4);
        System.out.println(Math.ceil(4.5));
    }
}
```

## Typecasting / Type Conversions

You can only cast a variable if you are casting it to a type that is larger than the one it was previously. The expression Polack used is that you cannot fit into super skinny jeans, but you can fit into bigger pants.

```java
double dnum;
float fnum;
int inum;
dnum = (double)fnum * (double)inum;
```

## Char vs String

`String`s are initialized in Java with double quotes while `char`s are initialized with single quotes

```java
char initial = 'j';
String name = "Jennifer";
```

Characters can be read in as an integer.



## Random Numbers

1. Import `java.util.Random;`
2. Declare the random number generator
3. Initialize with `new`
4. Use it



```java
import java.util.Random;
public class RandTest {
    public static void main(String[] args) {
      Random rand;
      rand = new Random();
      int number = rand.nextInt(100); // Random generates number between 0-99
    }
}
```

How do you generate numbers in a different range?  [50, 150]

```java
rand.nextInt(100); // 0-99
rand.nextInt(101) // 0 - 100
rand.nextInt(101) + 50 //50-150
```

In more general terms

```java
rand.nextInt(end - start + 1) + start
```

