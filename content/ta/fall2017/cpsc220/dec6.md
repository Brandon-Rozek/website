# Final Review December 6

## Classes

Here is how you can create a class called "Employee" with a non-default constructor (a constructor that takes parameters) and a getter and setter

```java
public class Employee {
  // Our private variables
  private String name;
  private double salary;
  // Non-default constructor
  public Employee(String name, double salary) {
    this.name = name;
    this.salarly = salary;
  }
  // This is a getter
  public string getName() {
    return name;
  }
  public double setSalarly(double salary) {
    this.salary = salary;
  }
}
```

## For Loops + Arrays

For loops are constructed in the following way

`for (initialization; condition to stop; increment to get closer to condition to stop)`

```java
//Assume an array with variable name array is declared before
for (int i = 0; i < array.length; i++) {
  // This code will loop through every entry in the array
}
```

Note that you don't always have to start from zero, you can start anywhere from the array.

## For Loops + Arrays + Methods

This is an example of how you can take in an array in a method

```java
public static boolean isEven(int[] array) { // <-- Note the int[] array
  for (int i = 0; i < array.length; i++) { // Iterate through the entire array
    // If you find an odd number, return false
    if (array[i] % 2 == 1) {
      return false;
    }
  }
  // If you didn't find any odd numbers, return true
  return true;
}
```

## File I/O

Let's say that you have the following file

```
4
chicken
3
salad
```

And you want to make it so that you take the number, and print the word after it a certain number of times. For this example we would want to see the following

```java
chicken chicken chicken chicken
salad salad salad
```

Here is the code to write it

```java
public static void printStrings() {
  FileInputStream file = new FileInputStream("stuff.txt"); // File contents are in stuff.txt
  Scanner scnr = new Scanner(file); // Scanner takes in a file to read
  while (scnr.hasNext()) { // While there are still stuff in the file to read
  	int number = scnr.nextInt(); // Grab the number
    String word = scnr.next(); // Grab the word after the number
    // Print the word number times
    for (int i = 0; i < number; i++) {
      System.out.print(word); 
    }
    // Put a new line here
    System.out.println();
  }
  
}
```

## Recursion

Look at handout and carefully trace recursion problems

## 2D Arrays

Declare a 2D int array with 4 rows and 7 columns

```java
int[][] dataVals = new int[4][7];
```

A 2D array with 4 rows and 7 columns has 7 * 4 = 28 entries.



If you want to sum up all the numbers in a 2 dimensional array, do the following

``` java
// Assume numbers is declared beforehand
int sum = 0;
for (int i = 0; i < numbers.length; i++) { // Loop through every row in the 2D array
  for (int j = 0; j < numbers[i].length; j++) { // Loop through every column in a row
    // This code now looks at one entry in a 2D array
    sum += numbers[i][j];
  }
}
```

