# November 6th Lecture

## Compare cont.

Continuing from last week's topic, writing a function called `compare` in your custom class.

For example, for your project:

```java
public bool compare(ResearchProject right, int type) {
  if (type == 0) { // Is last lastname greater than right lastname alphabeticallly
    if (lastname.compareTo(right.lastname) > 0) {
      return true;
    } else {
      return false;
    }
  } else if (type == 1) { // Implement a different type of comparison
    
  }
}
```

You can then use the sorting algorithms discussed previously to sort the ResearchProjects using the `compare` method.

## File IO

First start by importing the required libraries. 

```java
import java.io.FileInputStream;
import java.io.IOException; // For error handling
import java.io.FileNotFoundException; // For error handling
import java.util.Scanner;
```

Then inside your main method which throws an IOException (see example "Reading the filename from the keyboard")

```java
FileStream file;
Scanner in;
try { // Try something
  file = new FileInputStream("test.txt");
  in = new Scanner(file);
} catch (FileNotFoundException e) { // Catch IF it fails
  System.out.println("File not found.");
  in = new Scanner(System.in); // Read from the keyboard instead
}
// Read the file now....
String name = in.nextLine();
```

Before we had linked the Scanner to the keyboard, now we're doing it to a file.

### Try-Catch

In the code above you see what's called a try-catch block. That means that if something was to happen in the execution of the code. Instead of just crashing as we have been seeing normally. We can deal with the error. In the example above you saw that the program reads from the keyboard instead of the file

### Reading the filename from the keyboard

```java
public static void main(String[] args) throws IOException {
  FileInputStream file;
  Scanner in, scnr;
  // Connect one scanner to the keyboard to get the filename
  scnr = new Scanner(System.in); 
  
  System.out.print("Enter file name: ");
  String filename = in.nextLine();
  
  // Repeat code from previous example
  FileStream file;
  Scanner in;
  try {
    file = new FileInputStream(filename); // Only this line changed
    in = new Scanner(file);
  } catch (FileNotFoundException e) {
    System.out.println("File not found.");
    in = new Scanner(System.in);
  }
  String name = in.nextLine();
  // ....
}
```

The main throws the IOException since we don't deal with it in any of the catch blocks.



### Reading names of people from a file into an array

Let's say we have a file with the following in it

```
3
Paul
Peter
Mary
```

3 is to indicate the number of names in th file.

Let's write code in order to read these names into an array!

```java
import java.io.FileInputStream;
import java.io.IOException;
import java.io.FileNotFoundException;
import java.util.Scanner;
public static void main(String[] args) throws IOException {
  FileInputStream file;
  Scanner in, scnr;
  scnr = new Scanner(System.in); 
  
  System.out.print("Enter file name: ");
  String filename = in.nextLine();
  
  FileStream file;
  Scanner in;
  try {
    file = new FileInputStream(filename); // Only this line changed
    in = new Scanner(file);
  } catch (FileNotFoundException e) {
    System.out.println("File not found.");
    in = new Scanner(System.in);
  }
  
  // For the size of the array, get the first number in the file
  int size = in.nextInt();
  String[] nameArray = new String[size];
  for (int i = 0; i < size; i++) {
    namesArray[i] = in.nextLine();
  }
  
  // Now all the names in the file is in the namesArray
}
```

