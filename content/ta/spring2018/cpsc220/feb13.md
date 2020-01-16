# Lecture for February 13

## Loops

###Why Loops?

While some check is true, repeat the work.

While the cookies aren't baked, keep baking

### Loop Building Process

1. Identify one test that must be true when the loop is finished
2. Use the **opposite** form of the test
3. Within loop, make *progress* towards completion of the goal.

### While syntax

```java
while (expression) {
  // Loop body executes if expression is true
}
// Statements execute after expression is false
```

### Getting Input (Songs in a Playlist Psuedocode)

```java
// Ask user about first song
while (user says play next song) {
    // play next song
    // ask user about next song
}
```

### Nested Loops

You can have loops inside loops

```java
int outer = 1;
while (outer < 4) {
  int inner = 1;
  while (inner < 4) {
    System.out.println(outer + ":" + inner);
    inner++;
  }
  outer++;
}
```

This code does the following

```reStructuredText
1:1
1:2
1:3
2:1
2:2
2:3
3:1
3:2
3:3
```

### Break Down the Problem

Never write the entire program at once! This makes it incredibly hard to debug. Instead break it into small parts.

Write one part -> debug until it works

Write second part -> debug until it works

This way you know which part of your code failed, instead of having everything fail.