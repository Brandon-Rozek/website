# Lecture Notes October 11

## Global Variables

Global variables is where you don't declare a variable inside a method. This is generally not a recommended practice. It is recommended to declare variables inside methods so that it is easier to reuse code.

```java
public class mainDriver {
  public static int globalVariable = 5; // I am a global variable
  public static void main(String[] args) {
      int localVariable = 4; // I am a local variable
  }
}
```

## String Formatting

You can format strings in java by using the `printf` method in System.out.

Format strings work by using placeholders starting with `%` to specify where to place the value of a variable.

General format of command

```java
//System.out.printf(FormatString, variable1, variable2, ....)
String s = "The number is";
int x = 5;
System.out.printf("%s %d", s, x); // Prints "The number is 5"
```

If you want to print out money, you can do it through the following

```java
float tax = 0.45698;
System.out.printf("The tax is %.2f"); //prints "The tax is 0.46"
```

## Floating point precision

Due to how computers store non-integers, math can be non-precise after some mathematical operations. It is therefore advantageous to do operations on integers to the level of precision you want.

For example, instead of working in dollars, work in pennies since it's the smallest division we care about.



### ArrayList

Standard arrays are static, meaning they have no ability to grow. Instead of doing the operations we described last class, in order to add something to an array. We can use something called an `ArrayList` instead.

The methods in the `ArrayList` library are useful abstractions to make the life of a programmer easier.

ArrayLists can also hold only one type. The type cannot be a primitive like a standard array. Instead it must be a class representing the desired type.

int -> Integer

double -> Double

char -> Character

float -> String

To declare and initialize an `ArrayList`

```java
import java.util.ArrayList;
public class ArrayListTest {
    public static void main(String[] args) {
      ArrayList<Integer> numbers = new ArrayList<Integer>();
      ArrayList<String> names = new ArrayList<String>();
    }
}
```

`ArrayList`s has a variety of different methods that can be used to access/manipulate it

- get
- set
- add
- clone
- clear
- size

If you want to add the numbers 1 through 10 into the `ArrayList` of numbers

```java
for (int i = 1; i < 11; i++) {
    numbers.add(i);
}
```

To print out the entire contents of the `ArrayList`

```java
for (int i = 0; i < numbers.size(); i++) {
    System.out.println(numbers.get(i));
}
```

How can you replace a value?

```java
int n = 5; // Make this the number you wish to replace
int i = 0;
while (i < numbers.size() && numbers.get(i) != n) {
    i++;
}
if (i == numbers.size()) {
    System.out.println(n + " not found.");
} else {
  int r = 10; // Make this the value you want to replace n with
  numbers.set(i, r);
}
```

The `remove` method removes an item given an index. This shifts all the elements above the removed index down.

```java
numbers.remove(3); // Removes the element in the third index
```

The `add` method can also take an index. It pushes all the elements at the index specified up.

```java
numbers.add(3, 5); // Adds the number 5 to the third index
```

You can clone an array using the `clone` method

```java
ArrayList<Integer> numbers2 = new ArrayList<Integer>();
numbers2.clone(numbers); // Clones numbers into numbers2
```

