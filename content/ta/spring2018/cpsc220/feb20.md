# Lecture for February 20th

## Reading a File

You can get input from a file instead of from the terminal

```java
FileInputStream fileIn = new FileInputStream("myFile.txt");
// Our familiar Scanner
Scanner scnr = new Scanner(fileIn);
// We can use our usual Scanner methods
String line = scnr.nextLine();
fileIn.close(); // Remember to close the file when you're finished with it!
```

### Reviewing Scanner Methods

To understand some of the Scanner methods we need to be aware of the "newline" character. This character is equivalent to the `Enter` button on the keyboard.

`scnr.nextLine()` This get's all the characters in the buffer up to the newline character.

`scnr.next()` Grabs the characters in the next "token". Tokens are usually separated by any whitespace type character (spaces, enters, tabs, etc.)

## Writing to a File

Prints information to a file instead of to the screen

```java
FileOutputStream fileOut = new FileOutputStream("myOutfile.txt");
PrintWriter out = new PrintWriter(fileOut);
out.println("Print this as the first line.");
out.flush(); // Pushes the file changes to the file
fileOut.close(); // If you forget this then it won't remember your changes
```

## Arrays

Arrays are containers of fixed size. It contains a fixed number of values of the **same type**. (Ex: 10 integers, 2 strings, 5 booleans)

Declaration

```java
int[] array; // This declares an integer array
```

Initialization

```java
array = new int[7]; // This states that this array can hold up to 7 integers
```

Storing a value in an array

- Square bracket notation is used

```java
int[] array = new int[7];
array[0] = 5; // Stores 5 into the first slot
```

Now let us attempt to retrieve the value

```java
int temp = array[0];
System.out.println(temp); // Prints "5"
```

### Traversing an Array

Let's say we have the following array

```java
int[] numbers = {3, 5, 2, 7, 9};
```

Let's print out each of the values in the array

```java
for (int i = 0; i < numbers.length; i++) {
    System.out.print("value in " + i " is " + numbers[i]);
}
```

### Finding the maximum value in an Array

```java
int highest = numbers[0];
for (int i = 0; i < numbers.length; i++) {
    if (numbers[i] > highest) {
        highest = numbers[x];
    }
}
```

