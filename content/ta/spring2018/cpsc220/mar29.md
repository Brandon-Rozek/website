# Lecture for March 29th 

## Enumerated Types

These represent a fixed set of constants and include all possible values within them.

Let's look at coins. On a daily basis in the US, we use the following coins:

- Penny
- Nickel
- Dime
- Quarter

Other examples include the days of the week, clothes sizes, etc.

## Enum Syntax

Let's define an `enum` type

```java
public enum Coin { PENNY, NICKEL, DIME, QUARTER}
```

Now declare and initialize a variable

```java
Coin myCoin = Coin.PENNY
```

## Arrays vs ArrayList

Arrays require you to say upfront, how many slots you need. ArrayLists are more flexible since you can change the length of the array during Runtime. 

Arrays can store objects and primitives such as `int`, `char`, `boolean`, etc.

ArrayLists can only store objects.

### How to declare an ArrayList

```java
ArrayList<objectType> list = new ArrayList<objectType>();
```

### Differences between getting the length of the array

**Array**

```java
int length = array.length;
```

**ArrayList**

```java
int length = array.size();
```

## For Each Loop

This is a special loop in where you tell it to go through all the elements of the array, without specifying an index.

```java
for (String b : buildings) {
    System.out.print(b);
}
```

