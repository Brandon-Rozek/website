---
title: "Recitation 11: Exam 2 Review"
date: 2022-04-04T15:40:12-04:00
draft: false
tags: []
math: false
---

## Conceptual Questions
1. When must a representation invariant hold?

2. What's the difference between a representation invariant and an abstract function?

3. Which type of testing only considers the specifications and not the implementation?

4. What is the difference between overriding and overloading a method?

5. Provide an example of representation exposure.

6. Are Java subtypes true subtypes? Why or why not?


## Overloading vs Overriding: Spaghetti Code Edition

Consider the following Java code

```java
class A {
void m(A a) { System.out.println("AA"); }
void m(B a) { System.out.println("AB"); }
void m(C a) { System.out.println("AC"); }
}
class B extends A {
void m(A a) { System.out.println("BA"); }
void m(B a) { System.out.println("BB"); }
void m(C a) { System.out.println("BC"); }
}
class C extends B {
void m(A a) { System.out.println("CA"); }
void m(B a) { System.out.println("CB"); }
void m(C a) { System.out.println("CC"); }
}
A a1 = new A();
A a2 = new B();
A a3 = new C();
B b1 = new B();
B b2 = new C();
C c1 = new C();
```
1. Fill in the following table with the output of `row.m(col)`

|        | a1 | a2 | a3 | b1 | b2 | c1 |   
|---     |--- |--- |--- |--- |--- |--- |
| **a1** |    |    |    |    |    |    |
| **a2** |    |    |    |    |    |    |
| **a3** |    |    |    |    |    |    |
| **b1** |    |    |    |    |    |    |
| **b2** |    |    |    |    |    |    |
| **c1** |    |    |    |    |    |    |

2. How would the grid change if I print it like below?

```java
A[] all = {a1, a2, a3, b1, b2, c1};
for (A some_a : all) {
    for (A some_a2 : all) {
        some_a.m(some_a2); System.out.print(" ");
    }
    System.out.println("");
}
```

|        | a1 | a2 | a3 | b1 | b2 | c1 |   
|---     |--- |--- |--- |--- |--- |--- |
| **a1** |    |    |    |    |    |    |
| **a2** |    |    |    |    |    |    |
| **a3** |    |    |    |    |    |    |
| **b1** |    |    |    |    |    |    |
| **b2** |    |    |    |    |    |    |
| **c1** |    |    |    |    |    |    |

## Generics and Advanced Typing

Consider the following Java code:

```java
class Mammal {}
class Cow extends Mammal {}
class Horse extends Mammal {}
class ToyHorse extends Horse {}


Object o = new Object();
Horse h = new Horse();
ToyHorse t = new ToyHorse();
List<? extends Mammal> lem = new ArrayList<>();
List<? extends Horse> leh = new ArrayList<>();
List<? super Horse> lsh = new ArrayList<>();
```

For each of the following, note whether or not it will compile.
1. `lem.add(h);`
2. `lsh.add(t);`
3. `lsh.add(o);`
4. `lem.add(null);`

Assume that the ArrayList have elements in them.

5. `h = lsh.get(0);`
6. `m = leh.get(0);`
7. `o = lsh.get(0);`

## Equivalence Relations

1. What are the three properties that you need to show in order to prove that the method is an equivalence relation.

2. Is the following an equivalence relation? If so, prove. Otherwise provide counterexample.

```java
class String {
    public boolean equals(String other) {
        for (int i = 0; i < this.length; i++) {
            if (this.contents[i] != other.contents[i]) {
                return false;
            }
        }
        return true;
    }
}
```

3. Is the following an equivalence relation? If so, prove. Otherwise provide counterexample.

```java
class FuzzyNumber {
    public boolean equals(FuzzyNumber other) {
        // Check: this - 0.5 <= other <= this + 0.5 
        return this.number - 0.5 <= other.number && other.number <= this.number + 0.5;
    }
}
```

4. Is the following an equivalence relation? If so, prove. Otherwise provide a counterexample.

```java
class FuzzyNumberEnhanced {
    public boolean equals(FuzzyNumberEnhanced other) {
        return this.number - other.number == 0
    }
}
```

