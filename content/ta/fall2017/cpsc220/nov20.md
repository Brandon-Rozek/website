# Lecture for November 20

## Adding a drawing panel to the GUI

You can't put swing and graphics together, therefore you need to make a seperate JPanels for swing and graphics.

Add necessary libraries

```java
import java.awt.*;
import java.awt.Graphics;
import java.awt.event.*;
import javax.swing.*;
```



```java
public class drawingWindow extends JPanel {
  JTextField field;
  JButton draw;
  DrawingPanel drawingPanel;
  
  public drawingWindow() {
    // Each new component would be vertically stacked upon each other
    setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
    
    JPanel swingSTuff = new JPanel();
    
    // Add things to the screen    
    draw = new JButton("Draw");
    field = new JTextField();
    swingStuff.add(field);
    swingStuff.add(draw)
    
    // Add the drawing panel onto the screen
    drawingPanel = new DrawingPanel(200, 400);
    add(drawingPanel);
    
    // Activate the listener if the button was pressed
    draw.addActionListener(new Listener());
  }
  
  // Add the listener to respond to events
  private class listener implements ActionListener {
    public void actionPerformed(ActionEvent event) {
      if (event.getSource() == draw) {
        drawingPanel.setFlag(1);
        // Repaints the screen so the oval can appear
        drawingPanel.repaint();
      }
    }
  }
  
  // Create the draw panel so we can add it to the screen
  private class DrawingPanel extends JPanel {
    private int width, height;
    DrawingPanel(int width, int height) {
      this.width = width;
      this.height = height;
      setPreferredSize(new Dimension(width, height));
    }
    public void setFlag(int flag) {
      this.flag = flag;
    }
  	public void paintComponent(Graphics g) {
    	super.paintComponent(g);
    
    	// Every time the flag is set, draw an oval at a random location and color
    	if (flag == 1) {
      	Random rand = new Random();
      	int x = rand.nextInt(width);
      	int y = rand.nextInt(height);
      	g.setColor(Color.RED);
      	g.fillOval(x, y, 20, 30);
    	}
  	}
  }
}
```

There are a myriad of different methods you can use. 

```java
// Assume width, height, y, x, etc are defined above 
public void paintComponent(Graphics g) {
  //....
  g.dispose(); // Flushes the graphics buffer
}
```

You have the traditional fill and draw methods. Fill creates the shape shaded in with a color. Draw creates an outline of the shape.

```java
  
// ...
g.fillRect(x ,y, width, height);
  g.drawRect(x, y, width, height);
  g.fillOval(x, y, width, height);
  g.drawOval(x, y, width, height);
  //g.drawPoly(parematers...);
  //g.fillPoly(parameters...);
  g.drawArc(x, y, width, height, startingAngle, sweepingAngle);
  g.fillArc(x, y, width, height, startingAngle, sweepingAngle);
```

You can also create complex shapes like a polygon. When adding points, you need to make sure you add them Clockwise or Counterclockwise (but NOT both)

```java
  Polygon tri = new Polygon();
  tri.addPoint(150, 10);
  tri.addPoint(175, 100);
  tri.addPoint(125, 100);
  // Add points clockwise or counterclockwise (NOT BOTH)
```

