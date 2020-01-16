# CPSC 220 Lecture 3

## Variables

Variable -- Storage of information

The type cannot change in a variable.

Examples of types include

- int
- float
- double
- String
- char
- boolean

Declaration: `int num;`

Initialization: `num = 5;`

Declaration + Initialization: `int num = 5;`

### Possible Errors

**You cannot declare a variable multiple times.**

Undefined variables are when you do not declare a variable before attempting to use it.

### Casting

You need to cast if you are attempting to lose data or store a larger memory type into a smaller one.

double -> float -> int **(casting required)**

```java
double gpa = 3.2;
int num1 = 10 * (int)gpa // 30
```





# Operations

The basic number operations are

- +
- -
- *
- /
- % *(the remainder)*

Examples

```java
0 % 2 // 0
1 % 2 // 1
2 % 2 // 0

3 % 2 // 1
4 % 2 // 0
5 % 2 // 1

3 % 5 // 3
7 % 5 // 2
```

You can test if something is even using modulus %

```java
// Assuming i was initiliazed to a value earlier
if (i % 2 == 0) {
  System.out.println("i is even");
} else {
  System.out.println("i is odd");
}
```

 # System input

Here is sample code using a Scanner as input

```java
import java.util.Scanner;
public class ScannerExample {
  public static void main(String[] args) {
    Scanner in;
    in = new Scanner(System.in);
    
    // Grab numerical values
    int num = in.nextInt();
    float gpa = in.nextFloat();
    double weight = in.nextDouble();
      
    // Grab a single character
    in.nextLine()
    char initial = in.next().charAt(0);
    
    // To get the entire line of a string
    in.nextLine();
    String name = in.nextLine();
  }
}
```

You need to use `in.nextLine()` to grab the carriage return that is left after grabbing a numeric value.



# Classes and Objects

Classes are a new type that you can have multiple things of.

These classes are blueprints that are made up of primitives or more basic types.

First create a Pet.java file (Name of the class must match the name of the file)

```java
public class Pet {
  private String name;
  private int years;
}
```

You can then use the Pet class in your main program. The terminology here is that you can create instances or objects of the class.

In PetTester.java

```java
public class PetTester {
  public static void main(String[] args) {
    Pet myPet;
    myPet = new Pet();
  }
}
```

**Both Pet.java and PetTester.java must be in the same directory/folder**

### Mutators/Accessors

Since the variables are private we cannot access them in the main program. To work around this, we can write what is called a mutator method.

```java
public class Pet {
  private String name;
  private int years;
  
  // Mutators
  public void setName(String n) {
      name = n;
  }
  public void setYears(int y) {
      if (y >= 0) {
          years = y;
      } else {
          System.out.println("No one is less than 0 years old.")
      }
  }
}
```

Now let's use these new methods

```java
public class PetTester {
  public static void main(String[] args) {
    Pet mypet;
    myPet = new Pet();
    myPet.setName("Fred");
    myPet.setAge(20);
  }
}
```

We need a method that will allow us to access the data type. Let's add accessors to our pet class.

```java
public class Pet {
  private String name;
  private int years;
  
  // Mutators
  public void setName(String n) {
    name = n;
  }
  public void setYears(int y) {
    if (y >= 0) {
      years = y;
    } else {
      System.out.println("No one is less than 0 years old.")
    }
  }
  
  // Accessors
  public String getName() {
    return name;
  }
  public int getYears() {
    return years;
  }
}
```

Now let's get some information from the pet object, such as the age.

```java
public class PetTester {
  public static void main(String[] args) {
    Pet mypet;
    myPet = new Pet();
    myPet.setName("Fred");
    myPet.setYears(20);
    
    int year = myPet.getYears();
  }
}
```



### Constructors

Constructors lets us initialize variables in the class without having to use mutator methods.

```java
public class Pet {
  private String name;
  private int years;
  
  // Default Constructor
  public Pet() {
    name = "";
    years = 0;
  }
  // Non-Default Constructor
  public Pet(int y, String n) {
    name = n;
    years = y;
  }
  
  // Mutator Methods
  public void setName(String n) {
    name = n;
  }
  public void setYears(int y) {
    if (y >= 0) {
      years = y;
    } else {
      System.out.println("No one is less than 0 years old.")
    }
  }
  
  // Accessor Methods
  public String getName() {
    return name;
  }
  public int getYears() {
    return years;
  }
}
```

Now let us see this in action.

```java
public class PetTester {
  public static void main(String[] args) {
    Pet yourPet = new Pet(10, "Fluffy");
  }
}
```

You can have as many constructors as you want, but they must be different.

Example:

```java
public class Pet {
  ...
  pet() {
    name = "";
    years = 0;
  }
  pet(int y, String n) {
    name = n;
    years = y;
  }
  pet(String n) {
    years = 1;
    name = n;
  }
  ...
}
```

