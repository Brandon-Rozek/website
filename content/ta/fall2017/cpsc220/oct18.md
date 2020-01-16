# October 18th

## ArrayLists in classes

```java
public class Numbers {
  private ArrayList<Integer> used;
  private ArrayList<Integer> unused;
  numbers () {
    // Debug: System.out.println("1. Constructor Entry Point");
    used = new ArrayList<Integer>();
    unused = new ArrayList<Integer>();
    // Debug: System.out.println("2, Constructor Size of ArrayLists" + used.size() + " " + unused.size())
  }
  // Adds the numbers 1-5 into the used ArrayList
  public void fillUsedArrayList() {
    for (int i = 0; i < 5; i++) {
        used.add(i + 1);
    }
  }
  // Move an item from the unused ArrayList to the used ArrayList
  public int moveIt(int index) {
    int temp = used.get(index);
    unused.add(temp);
    // Debug: System.out.println("Adding to used array:" + (i + 1));
    used.remove(index);
    return temp;
  }
  // The method below is created for debugging purposes
  public void printBothArrayLists() {
    // Print the used arraylist
    System.out.println("Used ArrayList");
    for (int i = 0; i < used.size(); i++) {
        System.out.println(used.get(i));
    }
    
    // Print the unused arraylist
    System.out.println("Unused ArrayList");
    for (int i = 0; i < unused.size(); i ++) {
        System.out.println(unused.get(i));
    }
  }
}
```

Recall that you can compile the code above but you cannot run it. To run code, you must have a main method.

## NumberTester

```java
public class NumberTester {
    public static void main(String[] args) {
      Numbers list;
      list = new Numbers();
      list.fillUsedArrayList();
      list.printBothArrayLists();
    }
}
```





## Difference between Array and ArrayList

An Array is a **static** structure of contiguous memory of a single type.

An ArrayList is a **dynamic** structure of contiguous memory of a single type	



To get the size of an array you use `.length`

To get the size of an ArrayList you use `.size()`