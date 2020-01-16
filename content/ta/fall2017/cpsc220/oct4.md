# Lecture on October 4th

## Pass by Copy vs Pass by Reference

### Pass by Copy

When you pass a primitive type into a method (int, char, double, float, etc), it makes a copy of the value of the variable and brings it into the method

### Pass by Reference

When you pass an array into a method (int[], char[], double[], etc[]), it passes in the reference of the variable into the method. In other words, you give the actual array into the method and allows the method to change it.

### What's the Implication?

If you change the primitive in a method, it doesn't actually change the value of the variable.

If you pass in an array and change it in the method, it has been permanently changed outside the method as well.

### How do I make it so I can't change my array by accident?

Use the `final`keyword in the method header

```java
public static void printAll(final int[] array) {
    for (int i = 0; i < array.length; i++) {
        System.out.println("Number " + (i + 1) + " is " + array[i])
    }
}
```

