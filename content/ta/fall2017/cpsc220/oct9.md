# Lecture Notes October 9th

## Arrays (Cont.)

### Another way of Array Initialization

```java
String[] names = {"Jennifer", "Noodle", "Fluffy", "Rosie", "Cinnamon", "Brianne", "Oliver"}
```

Everything between the `{}` is the initial values in the names array in the order that it is written.

Recall that arrays are of a fixed size. The `names` array above has 7 elements.

### What can I do if I want to add something to the names array?

Do the following steps:

1. Create an empty array with the same size as the array
2. Take all the contents in the array and store it in a temporary array
3. Set names equal to another array of a bigger size
4. Take all the contents in temp and store it back to the array of choice
5. Add an element to the array by index

```java
// (1)
String[] temp = new String[7];
// (2)
temp.clone(names);
// (3)
names = new String[20]; // Now it can hold up to 20 names
// (4)
names.clone(temp);
// (5)
names[7] = "New name!";
```

