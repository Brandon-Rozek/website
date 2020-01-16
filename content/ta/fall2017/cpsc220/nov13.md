# Lecture for November 13

## File IO (Cont.)

Last class we talked about reading from files, we can also write to files.

### Import necessary libraries

First you must import all of the necessary libraries

```java
// To read 
import java.util.Scanner; 
import java.io.FileOutputStream;
// To Write
import java.io.FileReader;
import java.io.PrintWriter;
// For Exception Handling
import java.io.IOException;
```

Then in your main, declare a `FileOutputStream` and `PrintWriter`

```java
FileOutputStream file;
PrintWriter print;
```

### Try-Catch-Finally

Create a try block to open a file for writing

```java
try {
      // If the file doesn't exist, it'll create it
      file = new FileOutputStream("output.txt"); 
      print = new PrintWriter(file);
} catch (IOException except) {
      // Prints out the error message
      System.out.println("File error " + except.getMessage()); 
} 
```

Adding a finally block allows the program to clean up before it closes

```java
    try {
      file = new FileOutputStream("output.txt"); 
      print = new PrintWriter(file);
    } catch (IOException except) {
      System.out.println("File error " + except.getMessage()); 
    } finally { // It starts here!
      delete file;
      delete print;
      file.close();
      return;
    }
```

### Write to the file :)

Then you can write the to file!

```java
// Do you notice the following methods?
  print.println("Your number is");
  print.print("My name is..\n");
  print.printf("%s %d", "Hello ", 5);
  print.flush(); //Clears the output stream
  file.close(); //Closes the file

```

Extra Note: Disk fragmentation is a way of cleaning up memory that isn't being used by any of the code on your computer. 

## Swing Graphics

### Importing Necessary Libraries



You need to import all the necessary libraries first

```java
import javax.swing.*;
import java.awt.FlowLayout;
import java.awt.event.ActionListener;
```

### Changing the class header

Your class file needs to extend `JFrame` that way it can use a bunch of the already existent code written for Swing applications

```java
public class firstGUi extends JFrame {
  //....
```

### Swing Components

Java Swing makes use of what is called Swing Components. These are basic building blocks of GUI items you can add to the screen. For example, a checkbox, a radio button, text field. These are all swing components.

I wrote a blog post back in the summer which is an overview of them. You can check it out here: https://brandonrozek.com/2017/06/java-swing-components/

Inside your `firstGUI` class, declare some Swing components you would like to use in the program

```java
public class firstGUI extends JFrame {
  JButton button1;
  JTextArea area;
  JTextField text;
  // ....

```

### Constructor

You need to create a constructor for this class that way you can initiate all of the swing component values.

```java
// ...
JButton button1;
JTextArea area;
JTextField text;

// Begin Constructor
firstGUI() {
  // Define the components
  JLabel name = new JLabel("Enter in your name:");
  text = new JTextField("Jennifer", 20); // 20 characters long, default value: Jennifer
  area = new JTextArea(10, 10); //Width and Height is 10 characters big
  JScrollPane sp = new JScrollPane(area); //Adds a scroll bar for the text area
  button1 = new JButton("Press Me");
  
  // Set the Layout
  // FlowLayout organizes each of the components top to bottom, left to right
  setLayout(new FlowLayout()); 
  
  // Add the components to the screen
  add(name);
  add(text);
  add(sp); // never add the textarea when surrounded by a ScrollPane
  add(button1);
}
```

### New Main Method

Finally, you need to create the Main method which will initiate it all

```java
public static void main(String[] args) {
  firstGUI myFrame = new firstGUI();
  
  // End the program when the 'x' button (not keyboard) is pressed
  myFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
  
  myFrame.setTitle("My title"); // Titles the window
  myFrame.pack(); // Packs it all into the frame
  myFrame.setVisible(true); // Makes the frame appear on the screen
}
```

### Making it interactive

You need to change your class header to the following

```java
public class firstGUI extends JFrame implements ActionListener {
  // ...
```

Then in your class, add the following method

```java
@Override public void actionPerformed(ActionEvent event) {
  // Do stuff as a result of an event here
  area.append("You Pressed the Button");
}
```

To make it actually activate as a result of an event. You need to attach it to a swing component.

For example, I want the code in `actionPerformed` to activate in result of a button press.

Add the following line to your code in the constructor.

```java
//...
button1 = new JButton("Press Me");
button1.addActionListener(this); // New Code
//....
```



### Identifying Button Pressed

How do you know which button was pressed in the `actionPerformed` method?

You can use `event.getSource()` to find out.

Example:

```java
@Override public void actionPerformed(ActionEvent event) {
  if (event.getSource() == button1) { // Replace button1 with appropriate variable name
    // Do things as a result of a specific button being pressed
  }
}
```

### Summary

To use Swing, do the following steps

1. Import Libraries
2. Declare J___ variables
3. New the J___ variables
4. Add the J___ variables to the frame
5. Add the `ActionListener` to the components you wish to monitor