# Lecture for October 23

## Two-Dimensional Arrays

You can think of a two dimensional array as a grid that is organized by rows then columns.

To declare a two dimensional array do the following

```java
int[][] grid  = new int[5][5];  // Declares a 2D array of 5 rows and 5 columns
```

You can have as many dimensions as you want. For graphics a 3-dimensional array would render 3D points.

It doesn't have to be inherently visual though, you can have the n-dimensional array look at the interaction between n different variables. For example, the relationships to different questions in a survey.

Strings are essentially a char array with extra methods attached. We can imitate an array of strings with a 2D char array.

```java
char[][] helloWorld = new char[5][5];
hello[0][0] = 'h';
hello[0][1] = 'e';
hello[0][2] = 'l';
hello[0][3] = 'l';
hello[0][4] = 'o';
hello[1][0] = 'w';
hello[1][1] = 'o';
hello[1][2] = 'r';
hello[1][3] = 'l';
hello[1][4] = 'd';

```

## Nested-For Loops

To access the elements in a 2D array, you need to use a nested for-loop. 

Here is how you print out the hello world example above

```java
for (int row = 0; row < helloWorld.length; row++) {
  for (int col = 0; col < helloWorld[row].length; col++) {
      System.out.print(helloWorld[row][col]);
  }
  System.out.print(" ")
}
```

The code above prints out "hello world"



## 2D Arrays in methods

You can write a get like method in the following way

```java
public static void get(int[][] array, int row, int col) {
    return array[row][col];
}
```

Arrays in Java are pass by reference not pass by value. Meaning that if you change the array within the method then it will change outside the method.

```java
public static void insert(int[][] array, int row, int col, int numToInsert) {
    array[row][col] = numToInsert;
}
```

To make it not be able to change the array inside the method, use the keyword `const` inside the method header. To code below will throw a compiler error.

```java
public static void insert(const int[][] array, int row, int col, int numToInsert) {
    array[row][col] = numToInsert; // This line will throw an errror
}
```

