# Oct 30 Lecture

## Sorting

### Bubble Sort

These instructions are to sort in descending order, to sort in ascending order just negate the condition.

This sort is a series of iterations, for each iteration you go to the bottom of the array. Then compare if the value is greater than the element before it. If it is, then you 

1. Go to the bottom of the array
2. Compare the value to the one before it
   1. If it's greater than the element before it -> swap
3. Move on to the value before it and repeat step 2.

Once you go through an iteration, the last thing being compared is the greatest value of the entire array. That means you don't have to check it every time anymore. 

Keep going through all the iterations until n, where n is the size of the array, iterations have been completed.

### Swapping Values

If you try to swap variables by saying

```java
y = x;
x = y;
```

then you'll end up overwriting y's value with x and both variable would have x's value.

If you want to actually swap variables, you must create a temporary variable that saves y's value so that it can be properly assigned to x.

```java
int temp;
temp = y;
y = x;
x = temp;
```

### Implementation (Not Complete)

```java
// Each iteration
for (int j = 0; j < array.length - 1; j++) {
  // Each element in the list
  for (int i = 0; i < array.length - 1; i++) {
    // Is the element greater than the one after it?
    if (array[i] > array[i + 1]) {
     // Swap
      int temp = array[i + 1];
      array[i + 1] = array[i];
      array[i] = temp;
    }
  }
}
```

This here compares each of the values each time. If you remember before, I said that you don't have to compare the topmost each time.

### Implementation

To change this,  just change the second loop condition

```java
// Each iteration
for (int j = 0; j < array.length - 1; j++) {
  // Each element in the list
  for (int i = 0; i < array.length - 1 - i; i++) { // Note this line
    // Is the element greater than the one after it?
    if (array[i] > array[i + 1]) {
     // Swap
      int temp = array[i + 1];
      array[i + 1] = array[i];
      array[i] = temp;
    }
  }
}
```

## Compare

In Java, you can compare numbers, strings, and even your own customized objects. To compare your own customize object, you must write a method called `compare` in your class.

### To use your compare method in the sorting algorithm

```java
// Each iteration
for (int j = 0; j < array.length - 1; j++) {
  // Each element in the list
  for (int i = 0; i < array.length - 1 - i; i++) {
    // Is the element greater than the one after it?
    if (array[i].compare(array[i + 1])) { // Note this line
     // Swap
      int temp = array[i + 1];
      array[i + 1] = array[i];
      array[i] = temp;
    }
  }
}
```

