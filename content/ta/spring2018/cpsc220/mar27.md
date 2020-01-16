# Lecture for March 27

## In the Real World...

Objects are known for having characteristics. A car has on average 4 wheels, 2-4 doors, a steering wheel.

Objects can perform actions. A car can drive, hold cargo, and honk.

## In the Programming World...

Object-Oriented Programming

- Focuses on objects
- Are not linear
- Adds organization to a program
- Fits with human cognition (making abstractions)

## Class Structure

```java
public class Classname {
    // Fields
    // Constructors
    // Methods
}
```

## Fields

Fields are instance variables, they store values, help define state, and exist in memory for the lifetime of the object.

```java
public class Car {
    private double price;
    private double gas;
}
```

## Constructor

We can build an object through a constructor. It is a special kind of method, this method requires that you not have a return type and that you name it the same as the class itself.

Constructors help set default field values for the different properties of our class.

```java
public class Car {
    // Begin Constructor
    public Car(double cost) {
        this.price = cost;
        this.gas = 0;
    }
    // End Constructor
    private double price;
    private double gas;
}
```

**Note:** The `this` keyword refers to the object's fields. This helps keep it separate from other variables you can create in the method and the input parameters you receive.

## Accessor Method - "Getter"

We like to classify methods into two types, accessors and mutators.

Getter methods return a copy of an instance field. It does not change the state of the object.

```java
public double getPrice() {
    return this.price;
}
```

## Mutator Method - "Setter"

This type of method modifies an instance field. It does not return anything and changes the state of the object.

```java
public void setPrice(double cost) {
    this.price = cost;
}
```

## Example of Car Class In All Its Glory

```java
public class Car {
    // Instance Variables
    private int mpg;
    private double price;
    
    // Constructors
    public Car() {
        this.price = 0;
        this.mpg = 0;
    }
    public Car(double cost, int mpg) {
        this.price = cost;
        this.mpg = mpg;
    }
    
    // Accessors
    public double getPrice() {
        return this.price''
    }
    public int getMpg() {
        return this.mpg;
    }
    
    // Mutators
    public void setPrice(double cost) {
        this.price = cost;
    }
    public void setMpg(int mpg) {
		this.mpg = mpg;
    }
}
```

## Using Classes

Just like how we used the `Scanner` class, we can also use our new `Car` class.

```java
public class TestCar {
    public static void main(String[] args) {
        // Declare an object reference
        Car c;
        
        // Initialize the object
        c = new Car();
        
        // Update the fields of the object
        c.setPrice(3000);
        c.setMpg(22);
        
        // Print object information
        System.out.println("Price is " + c.getPrice() )
    }
}
```

