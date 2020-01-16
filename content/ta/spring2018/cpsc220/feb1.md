# Lecture for February 1st

## Control Structures

In this class we will talk about three types of control structures

- Sequential
- Selection
- Repetition

Sequential is what is most familiar to us. Write the lines from top to bottom and it executes it in that order

### Selection

Selection depends on the question of `if`. 

If it is raining, wear boots

```java
if (raining) {
  wearingBoots = true;
}
```

If you want something to happen also when it is not true, consider an `if-else` statement

If the light is off, turn it on.

Otherwise, turn it on

```java
if (lightIsOn) {
  lightIsOn = false;
} else {
  lightIsOn = true;
}
```

Sometimes you can have multiple branches depending on a condition. Let us take a stop light as an example

```java
if (light == "red") {
  car.stop()
} else if (light == "yellow") {
  car.slow()
} else {
  car.go()
}
```

## String comparison

There is a specific method in the `String` class when it comes to checking for string equality

```java
boolean equals(String s)
```

Let us look at an example

```java
String word = "hello";
boolean ans = word.equals("hello"); // Returns true
boolean ans2 = word.equals("Hello"); // Returns false
```

