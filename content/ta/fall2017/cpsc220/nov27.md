# Lecture for November 27

## Recursion

When doing recursion, make sure not to use loops.

Recursion is when a function makes a function call to itself.

It consists of two parts:

- Base Case: This tell it when to stop
- Smaller Caller Case: Helps you get closer to the base case

You can have one or more base cases or caller cases.

To teach recursion, we'll start with a problem that should be written iteratively (with loops) but we'll show how to do it with recursion.

### Example: Counting Down

```java
void CountDown(int number) {
  while (number > 0) {
    System.out.println(number + " ");
    number = number - 1;
  }
  System.out.println("Blast Off")
}
```

1. How does this loop stop? -- Base Case
2. How does this loop change each time through? -- Smaller caller case

Base Case: It stops when the number equals 0

```java
// Base Case
if (number == 0) {
  System.out.println("Blast Off");
  return;
}
```

Smaller Caller Case: It decreases number by 1

```java
// Smaller Caller Case
System.out.print(number + " ");
countDownRecursive(number - 1);
```

Put it together...

```java
void countDownRecursive(int number) {
  if (number == 0) {
    System.out.println("Blast Off");
  } else {
    System.out.print(number + " ");
    countDownRecursive(number - 1);
  }
}
```

Prints `10 9 8 7 6 5 4 3 2 1 Blast Off`

### Stack Snapshots

Every time you make a recursive call, it keeps track of all the local variables at the current function call and pushes it onto the stack.

That means if you make 10 recursive calls, you'll have 10 slots added onto the stack. If you want to return back to the beginning, you would need to return 10 times.

### Order Matters

Whether you do the recursive step first or some other action, it completely changes the output. Look at the following example that's similar to `countDownRecursive`.

```java
void countUpRecursive(int number) {
  if (number == 0) {
    System.out.println("Blast Off");
  } else {
    // Notice the swapping of the next two lines
    countUpRecursive(number - 1);
    System.out.print(number + " ");
  }
}
```

This would print out `Blast Off 1 2 3 4 5 6 7 8 9 10`

### Example: Summing up to a number

This would be our iterative solution

```java 
int sum(int number) {
  int sum = 0;
  while (number > 0) {
    sum += number;
    number--;
  }
  return sum;
}
```

How does this loop stop?

​	Same as before. Think about it, if the number you pass in is zero, what should be the result of sum? Zero. Since adding up from 0 to 0 is just 0.

```java
if (number == 0) {
  return 0;
}
```

How does this loop change each time through?

​	You want to update your sum, so return the sum of the next call to the current sum.

```java
return (number + sum(number - 1));
```

Putting it all together

```java
int sumRecursive(int number) {
  if (number == 0) {
    return 0;
  } else {
    return number + sumRecursive(number - 1);	
  }
}
```

### Example: Linear Search

How to do it iteratively.

```java
void linearSearch(int[] array, int number) {
  int i = 0;
  while (i < array.length && number != array[i]) {
    i++;
  }
  if (i == array.length) {
    System.out.println("Not Found");
  } else {
    System.out.println("Found");
  }
}
```

Base Case: There are two base cases, when it reaches the end of the array and when it finds the number

```java
if (array.length == i) {
  System.out.println("Not Found");
} else (array[i] == number) {
  System.out.println(number + " found at index " + i);
}
```

Smaller Caller Case: Check the next element

```java
linearSearchRecursion(number, array, i + 1);
```

Putting it all together...

```java
void linearSearchRecursion(int[] array, int number) {
  if (array.length == i) {
    System.out.println("Not Found");
  } else if (array[i] == number) {
    System.out.println(number + " found at index " + index);
  } else {
    linearSearchRecursion(number, array, i + 1);
  }
}
```

## Binary Search

This is a much more efficient search than the linear search we have been doing. The only condition is that your array must be sorted beforehand.

A regular linear search  `O(n)` -- Check at most all of the elements of the array.

Binary Search `O(log(n))` -- Checks at most `ceil(log(n))` elements of an array.

To demonstrate this with real numbers, let's take an array of 100 elements

- With linear search this will take at most 100 iterations
- With binary search this will take at most **7**.

Crazy right?



### Implementation

**Iterative approach**

```java
void binarySearch(int number, int[] array) {
  int lower = 0;
  int upper = array.length - 1;
  int mid = (lower + upper) / 2
  while (lower <= upper && array[mid] != number) {
    mid = (lower + upper) / 2;
    if (array[mid] < number) {
      lower = mid + 1;
    } else if () {
      upper = mid -1;
    }
  }
  if (lower > upper) {
    System.out.println("Not Found");
  } else {
    System.out.println(number + " found at index " + mid);
  }
}
```

**Recursive Approach**

Base Case: There are two cases, you either found it, or you made it to the end of the array without finding it

```java
if (lower > upper) {
  System.out.println("Not Found");
} else if (array[mid] == number) {
  System.out.println(number + " found at index " + mid);
}
```

Smaller Caller Case: Change the lower or upper bounds to cut the search in half

```java
if (array[mid] < number) {
  lower = mid + 1;
  binarySearchRecursive(number, array, lower, upper);
} else if (array[mid] > number) {
  upper = mid - 1;
  binarySearchRecursive(number, array, lower, upper);
}
```

Putting it together....

```java
binarySearch(int number, int[] array, int lower, int upper) {
  if (lower > upper) {
  	System.out.println("Not Found");
  } else if (array[mid] == number) {
  	System.out.println(number + " found at index " + mid);
  }
  else if (array[mid] < number) {
  	lower = mid + 1;
  	binarySearchRecursive(number, array, lower, upper);
  } else if (array[mid] > number) {
  	upper = mid - 1;
  	binarySearchRecursive(number, array, lower, upper);
  }
}
```

