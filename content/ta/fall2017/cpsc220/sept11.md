# CPSC 220 Lecture 4

## Practice Problem

1. Create a class called Car
2. - Create a private variable of int type called year
   - Create a private variable of String type called make
3. Create accessor methods for all data members.
4. Create mutator methods for all data methods.



```java
public class car { // begin car
  private int year;
  private String make;
  public int getYear(void) {
      return year;
  }
  public String getMake() {
      return make;
  }
  public void setYear(int y) {
    if (y > 1890) {
        year = y;
    } else {
        System.out.println(y + " is not a valid year.");
    }
  }
  public void setMake(String m) {
      make = m;
  }
}
```

Local variables are only existent within the curly braces that it is defined in.

## If Statements and Boolean Expressions

Boolean expressions return a boolean

```java
1 < 4; // 1 is less than 4: TRUE
3 > 5; // 3 is greater than 5: FALSE
5 == 5; // 5 is equal to 5: TRUE
5 != 5; // 5 is not equal to 5: FALSE
1 >= 1; // 1 is greater than or equal to 1: TRUE
5 <= 1; // 5 is less than or equal to 1: FALSE
```

 If statements only occur if the boolean expression is true, otherwise the `else` block is executed.

```java
if (true) {
  System.out.println("I am always printed");
} else {
  System.out.println("I am never printed");
}
```

You can only have one `else` per `if`. If you have an `if` you don't necessarily need an `else`

## Local vs Class Variables

If you have a local variable and the class variable sharing the same name, then the local variable is always used first.

```java
public class car { // begin car
    private int year;
  public void setYear(int year) {
     year = year;
  }
}
```

This is a redundant statement, it makes the argument that is passed in equal to itself.

To avoid this situation, use the keyword `this` to access the class variable

```java
public class car { 
  private int year;  
  public void setYear(int year) {     
    this.year = year;  
  }
}
```

The code above runs as expected.

Rewriting our class with `this`

```java
public class car { // begin car
  private int year;
  private String make;
  public int getYear(void) {
      return year;
  }
  public String getMake() {
      return make;
  }
  public void setYear(int year) {
    if (y > 1890) {
        this.year = year;
    } else {
        System.out.println(y + " is not a valid year.");
    }
  }
  public void setMake(String make) {
      this.make = make;
  }
}
```

## Unreachable Code

When the code hits a `return` statement, it stops executing the rest of the code in the method. Also throws an Unreachable Code Error.

```java
public int add(int x, int y) {
  return x + y;
  System.out.println("x + y = " + x + y);
}
add();
System.out.println("Hello");
```

Here the code above will not compile, though assuming the error doesn't exist then it would only print out "Hello"

## Constructors

You cannot have a private or protected constructors.

Constructors are used to initialize your objects.

You want to have the class variables to the left of the assignment statement.

```java
public class car {
  private int year;
  private String make;
  car() {
    year = 1890;
    make = "Ford";
  }
  car(int year, String make) {
    this.year = year;
    this.make = make;
  }
}
```



## Testers

Testers are useful to check that the class is implemented correctly.  Both the tester and the class have to be in the same folder/directory.

```java
public class carTester {
  public static void main(String[] args) {
    Car myCar; // Declaration
    myCar = new Car(); // Initilization
    Car yourCar = new Car(2009, "Hyundai"); // Declaration + Initialization
  }
}
```



## More about classes

```java
public class Car {
  private String name;
  private int odometer;
  public void setOdometer(int od) {
    odometer = od;
  }
  public void setName(String n) {
      this.name = n;
  }
  public void changeOilRequest(String name, int od) {
    if (name == this.name) {
      int difference = od - this.odometer;
      if (difference > = 3000) {
        // You can call other methods in the class
        setOdo(od);  // Equivalent to "this.setOdo(od);"
        this.odometer = od;
        System.out.println("Ready for oil change.");
      } else {
        System.out.println(name + " not ready for oil change.")
      }
    } // end if
  } // end changeOil request
} // end class
```

To call public methods outside the class use the variable name to do so.

```java
public class CarTester {
  public static void main(String[] args) {
    Car myCar = new Car();
    myCar.setName("Honda")
    myCar.changeOilRequest("Honda", 3400);
  }
}
```

## Math library

The `ceil` method rounds up while the `floor` method runs down.

```java
Math.ceil(3.2); // 4
Math.ceil(4.1); // 4
```

