# Lecture Notes for November 15th

Import the necessary libraries

```java
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
```

This time we'll be using the null layout. This will require you to set the x, and y positions of each of the elements on the screen

First we'll make a class called `GUILayout` which will extend `JPanel` and contain our layout and components

```java
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

public class GUILayout extends JPanel {
  private JButton one, two;
  private JTextField text;
  private JTextArea area;
  private int count; // Used to keep track of button pushes
  private int number = 0;
  
  GUILayout() {
    // Set the layout to the null layout
    setLayout(null);
    // Tells the computer that you wish to have the size of your program to be 500x500
    setPreferredSize(new Dimension(500, 500));
    
    // Create the buttons
    one = new JButton("Change color");
    two = new JButton("Count Pushes");
    
    // Set the x, y, width, height inside parenthesis
    // This places the buttons on the specified locations on the screen
    one.setBounds(10, 10, 100, 24);
    two.setBounds(120, 10, 100, 24);
    
    // Sets the color of the text of button 1 to blue
    one.setForeground(Color.BLUE); 
    
    // Add the components to the screen
    add(one);
    add(two);
    
    
    text = new JTextField("Today is Wednesday, a photographer is here.");
    text.setBounds(10, 40 ,480, 24);
    add(text);
    
    area = new JTextArea(20, 20); 
    // Wrap the text area into the scroll pane
    // This adds the scroll bars (vertical/horizontal)
    JScrollPane sp = new JScrollPane(area);
    sp.setBounds(10, 75, 490, 400);
    add(sp);
    
    // Bind the Listener class to the button one
    one.addActionListener(new Listener());
    
    // Bind it to two and text
    two.addActionListener(new Listener());
    text.addActionListener(new Listener());
   	
  }
  
  // Create the class for the listener
  private class Listener implements ActionListener {
    // Define what you want to occur after an event
    public void actionPerformed(ActionEvent event) {
      if (event.getSource() == one) {
        
      } else if (event.getSource() == two) {
      	count++;
      	// \n is needed to prevent scrolling
      	area.append("You pressed the button " + count + " times!"); 
      } else if (event.getSource() == text) {
        // Grab the number inside the text area and set it to the variable number
        number = Integer.paseInt(text.getText());
        number += 10;
        // add "" to number so that it converts number to a String
        text.setText(number + ""); 
        // Convert the number to a String
        String temp = Integer.toString(number);
        area.setText(temp);
      }

      
    }
  }
}
```

The main code is really short, you just need to extend `JFrame` and some short code seen last class to set it up.

```java
public class mainTester extends JFrame {
  public static void main(String[] args) {
    JFrame frame = new JFrame("Sample GUI"); // Sets the title to "Sample GUI"
    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    // Instantiate the GUILayout file you made before
    frame.getContentPane().add(new GUILayout()); 
  }
}
```

