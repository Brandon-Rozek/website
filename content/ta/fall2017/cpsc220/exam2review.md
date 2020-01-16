# Exam Review Partial Answer Sheet

Write a Java method to sum values of an array

```java
// Assume variable numbers is an array of 10 integers
int sum = 0;
for (int i = 0; i < numbers.length; i++) {
    sum += numbers[i];
}
```

Write a Java method to test if an array contains a specific value

```java
// Assume variable numbers is an array of 10 integers
int numWanted = 4;
boolean found = false;
for (int i = 0; i < numbers.length; i++) {
    if (numbers[i] == numWanted) {
      System.out.println("The number " + numWanted + " was found!");
      found = true;
    }
}
if (!found) {
    System.out.println("The number " + numWanted + " was not found!");
}
```

Write a Java method to find the index of an array element

```java
// Assume variable numbers is an array of 10 integers
int numWanted = 4;
boolean found = false;
for (int i = 0; i < numbers.length; i++) {
    if (numbers[i] == numWanted) {
      System.out.println("The index of number " + numWanted + " is " + i);
    }
}
```

How many lines will the following loop print when it is run?

```java
int i = 0;
while (i <= 6) {
  System.out.println("i is now " + (i));
  i++;
}
```

```
i is now 0
i is now 1
i is now 2
i is now 3
i is now 4
i is now 5
i is now 6
```

