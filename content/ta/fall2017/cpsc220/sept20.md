## Counting Loop

Looking at the following example code

```java
int i;
for (i = 0; i < 3; i++) { //begin for
  System.out.println("i = " + i); //body
} //end for
System.out.println("After loop, i = " + i);
```

`i = 0` is the initializing statement

`i < 3` is the conditional, that is when the loop ends

`i++` is the increment/decrement

`i++` is synonymous with `i = i + 1`

The initialization statement only occurs once at the beginning of the loop. 

### Execution Example

Let us go through this for loop example

- Let us set `i = 0`
- Is `i < 3`? Yes execute the body
  - The body executes an output of `"i = 0"`
- Now we increment `i ++`, i is now 1
- Is `i < 3`? Yes, 1 is less than 3. Execute body
  - The computer prints out  `"i = 1"`
- Increment `i++` i is now 2
- Is `i < 3`? Yes 2 is less than 3. Execute body
  - The computer prints out `"i = 2"`
- Increment `i++`, i is now 3
- Is `i < 3`?  No 3  is not less than 3
  - Don't execute body of loop

Exit loop. Print `"After loop, i = 3"`



### Condensing Syntax

You can also do the declaration in the initialization statement

```java
for (int i = 0; i < 3; i++) {
    System.out.println("i = " + i);
}
```

This now runs like above without the `"After loop, i = 3"` print. You cannot access the variable `i` outside the for loop since in this example, it belongs to the for loop's scope.



## Logic Expressions

### And Statements

With the AND operator `&&` both the left and right side needs to be true for the expression to be true.

```java
true && true // true
true && false // false
false && true // false
false && false // false
```

### Or Statements

With the OR operator `||` either the left or right side needs to be true for the expression to be true.

```java
true || true // true
true || false // true
false || true // true
false || false // false
```

### Examples

**Example**: Print out the number `n` if it is between 10 and 20 (inclusive)

```java
if (n >= 10 && n <= 20) {
    System.out.println(n);
}
```

**Example**: Print out the `age` if it is not of young adult age. Young adult range is from 18 to 39 (inclusive)

```java
if (!(age >= 18 && age <= 39)) {
    System.out.println(age);
}
```

Or you can use De Morgan's Law (for the curious)

```java
if (age < 18 || age > 39) {
    System.out.println(age);
}
```



## For Loops (Cont.)

### Backwards counting

You can use the loop to count backwards

```java
for (int i = 10; i > -1; i--) {
    System.out.println(i);
}
```

This prints the following

```java
10
9
8
7
6
5
4
3
2
0
```

### Rows-Columns

You can make rows and columns of asterisks

```java
for (int j = 0; j < someNumber; j++) { // Corresponds to rows
  for (int i = 0; i < someNumber2; i++) { // Corresponds to columns
    System.out.print("*"); 
  }
  System.out.println(""); // Goes to the next row
}
```

If `someNumber` equals `someNumber2`, then we have the same amount of rows as columns.

Let `someNumber` equal to 2 and `someNumber2` equal to 2

Output:

```
**
**
```

### Right Triangles

You can make a right triangle of Tilda with the following code

```java
for (int i = 1; i <= num; i++) { // Corresponds to the row
  for (int j = 0; j < i; j++) { // Corresponds to the column and stops at the current row number
      System.out.print("~");
  }
  System.out.println(""); // Moves to next row
}
```



##### What are for-loops used for? *Reusing code*

