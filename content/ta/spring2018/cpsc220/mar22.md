# Lecture on March 22nd

## Method Documentation

Java has a special way that you can document your methods such that it will create documentation for you if you follow the convention.

The Java API actually uses this technique to produce its own documentation.

To create this, indicate a method with special comments that begin with `/**` and ends with `*/`

It contains *block tags* that describe input and output parameters

`@param` and `@return`

### Example

```java
/**
 * @param y an integer to sum
 * @param x an integer to sum
 * @return the sum of x and y
 */
public int multiply(int x, int y) {
    return x + y;
}
```

## Passing a Scanner

We only want to create one **user input scanner** per program, we also only want one **file input scanner** per program.

If a method needs a scanner, you can pass the one you already created in as an input parameter.

## Array as Input Parameter

Primitive types (`int`, `char`, `double`, etc.) are passed by value. Modifications made inside a method cannot be seen outside the method.

Arrays on the other hand, is pass by reference. Changes made to an array inside the method can be seen outside the method.

```java
public static void main(String[] args) {
    int[] nums = {1, 3, 5, 7, 9};
    
    timesTwo(nums);
}
public static void timesTwo(int[] arr) {
    for (int i = 0; i < arr.length; i++) {
        arr[i] *= 2;
    }
}
```

At the end of the `timesTwo` method call, the variable `nums` would have `{2, 6, 10, 14, 18}`

## Sizes of Arrays

### Perfect Size Arrays

When we declare an array, Java automatically fills every slot of the array with the type in memory. So if you know that you need exactly 8 slots, then you only ask for 8.

### Oversize Arrays

This is when we don't know how many slots we need. Therefore, we ask for more than we think we'll need. That way we don't go out of bounds.

If we do this, then we don't know how many elements we have already inserted into the array. Since the length is the number of slots.

So we can create another variable, which will keep track of the index in where we can add the next element.

We use oversized arrays when the size of the array is unknown or may change.



