# Lecture for April 3rd

## Inheritance

The *base class*, *super class*, or *parent class* is the initial class that we are working with. Let's say that you want to *extend* the class, or add additional functionality. The class that inherits from the parent class is called the *child class*, *subclass* or *derived class*.

## Child Class Syntax

```java
public class Truck extends Car {
    // Truck Appropriate Fields
    // Necessary methods for truck
}
```

This code adds all the methods from Car into the Truck class. You can then add methods that is specific to a Truck into the Truck class.

A child class has all parent fields and access to all parent methods!

## Visibility Modifiers

Recall the words `public` and `private`

The `public` modifier makes the field/method accessible by any class

The `private` modifier makes the field/method only accessible within the method itself

The protected modifier makes the field/method accessible within the same class or any subclasses.

## Overriding a Method

You can override a parent class method by declaring a method in the child class with the same...

- name
- number of paramters
- parameter types

but this method would have different behavior!

