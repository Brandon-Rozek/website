# Lecture Notes Oct 2nd

## Array

`array` is not a reserved word, it's a concept. Arrays are able to hold multiple values under one name of the same type.

For instance, you can have an array of integers.

Properties of an array

- Size (n)
- index [0, n - 1]

You can declare arrays by saying the type '[]' and the name of the array

```java
int[] numbers;
double[] gpas;
float[] grades;
```

Before you can use the array, you must `new` it

```java
numbers = new int[10];
```

Where 10 is the size of the array.

You can combine both the declaration and initialization

```java
double[] points = new double[7];
```

You can access individual elements of the array by using its index. Indexes start from zero

```java
points[0] = 5.4; // The first element in the point array is 5.4
```

The `.length` property of an array gives the size of the array

## For-Loops + Arrays

You can print out each element in the array using a for loop

```java
for (int i = 0; i < numbers.length; i++) {
    System.out.println(numbers[i]);
}
```

You can ask a user to input a value to each element in the array

```java
for (int i = 0; i < points.length; i++) {
    System.out.print("Enter a number: ");
    points[i] = scnr.nextInt();
}
```

## While-Loops + Arrays

You can use a while loop to search the array

```java
int i = 0;
int number = 5;
// While the index is within the array size and the number isn't found
while (i != number.length && number != numbers[i]) {
    i++
}
if (i == numbers.length) {
    System.out.println(number + " was not found.")
} else {
    System.out.println(number + " was found at index " + i)
}
```

If you don't include the `i != number.length` you will obtain an `IndexOutOfBounds` error.

The example above is called a *Linear Search*. 

Linear searches work on an unsorted and sorted arrays.



## Methods + Arrays

You can pass an array into a method

```java
public static void exampleMethod(int[] sample) {
    // Do something
}
public static void main(String[] args) {
    int[] s = new int[30];
    exampleMethod(s);
}
```



## Do-While Loops

For-loops can run 0 or more times. If you want something to execute at least once. Use a do-while loop.

```java
do {
    // Code
} while (condition);
```

For example, to search at least once and asking whether the user wants to search again

```java
// Assume linearSearch and array are defined
char answer;
Scanner input = new Scanner(System.in);
do { 
  linearSearch(array, input);
  System.out.print("Do you want to search again? (Y/N) ");
  input.nextLine();
  answer = input.next().charAt(0);
} while( answer != 'N');
```

You can create any type of loop just by using a while loop.



## Example: Finding the Max

You can find the max of an array using the following method

```java
double max = arrayName[0];
for (int i = 1; i < arrayName.length; i++) {
    if (max < arrayName[i]) {
        max = arrayName[i];
    }
}
System.out.println("The max is " + max);
```



## Example: Summing up an array

You can sum the array using the following method

```java
double sum = 0;
for (int i = 0; i < arrayName.length; i++) {
    sum += arrayName[i];
}
System.out.println("The sum is " + sum);
```

