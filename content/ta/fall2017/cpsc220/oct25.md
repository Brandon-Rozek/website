# Lecture on Oct 25

## 2 Dimension Array of Objects

You can not only do a two dimensional array of primitive types, but you can also do two dimensional arrays of objects/classes.

```java
animalLocation[][] map;
map = new animalLocation[5][4];
```

Since we are dealing with classes, you cannot use this array right away. The code above creates the space in memory to store the objects. To have the animalLocation objects in the array, you must `new` each instance of the object.

```java
for (int i = 0; i < map.length; i++) {
    for (int j = 0; j < map[i].length; j++) {
        map[i][j] = new animalLocation();
    }
}
```

