# Lecture for January 25

## Strings

These are concatenated chars

```java
'd' + 'o' + 'g' // equivalent to "dog"
```

```java
"straw" + "berry" // strawberry
```

Strings are denoted by double quotes `""` rather than a string which is denoted by single quotes `''`

String is not a primitive type, it is a class. Hence, why it is capitalized in Java.

The `java.lang.String` is automatically imported in Java.

To declare and initialize a String

```java
String name = "Henry";
```

In memory it appears as

| H    | 'e'  | 'n'  | 'r'  | 'y'  |
| ---- | ---- | ---- | ---- | ---- |
|      |      |      |      |      |

### String Methods

```java
int length()
```

```java
boolean equals(String another)
```

```java
boolean startsWith(String prefix)
```

```java
boolean endsWith(String suffix)
```

```java
String substring(int start, int end)
```

```java
int indexOf(int ch)
```

```java
String toLowerCase()
```

### Using String Methods

```java
char first = name.charAt(0);
```

Remember in Java, that it starts counting from zero! If you try to access a letter that doesn't exist, it will produce an `IndexOutOfBounds` error.

## Errors

There are two types of errors, compile-type errors and run-time errors.  Later we will talk about debugging skills such as making "breakpoints" in your code so you can analyze the different variable values.

### Compile Time Errors

Compile time errors are generated due to syntax errors. Forgot a semicolon? Missing a brace? 

### Run-time Errors

These are logic errors. Not derived from syntax errors. An example of one that was discussed earlier is the `IndexOutOfBounds` error.



## Tricky Thing About Input

Let's talk about input right now. Let's say you have the following scenario

```java
Scanner input = new Scanner(System.in);
System.out.println("Enter pet's age: ");
int age = input.nextInt();
System.out.println("Enter pet's name: ");
String name = input.nextLine();
System.out.println("Enter pet's breed: ");
String breed = input.next();
```

Then when we start to run the program...

```reStructuredText
Enter pet's age: 
14
Enter pet's name:
Enter pet's breed:
Labradoodle
```

Why did it skip pet's name? Let's run through the process again

```reStructuredText
Enter pet's age: 
14 [ENTER]
Enter pet's name:
Enter pet's breed:
Labradoodle
```

Here the [ENTER] key gets saved into name.

To resolve this, just use an `input.nextLine()` to throw away that [ENTER]

```java
Scanner input = new Scanner(System.in);
System.out.println("Enter pet's age: ");
int age = input.nextInt();
System.out.println("Enter pet's name: ");
input.nextLine();
String name = input.nextLine();
System.out.println("Enter pet's breed: ");
String breed = input.next();
```





