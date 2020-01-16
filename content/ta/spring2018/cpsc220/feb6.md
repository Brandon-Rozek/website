# Lecture for February 6th

## If Statements -- Cont.

Inside the parenthesis of the `if` statement must be a boolean expression. This is an expression that evaluates to either `true` or `false`. We can do more complex boolean expressions through logical operators.

## Logical Operators

NOT `!a` this is true when `a` is false

AND `a && b	` this is true when both operands are true

OR `a || b` this is true when either a is true OR b is true

## Truth Tables

- Show all possible outcomes
- It breaks the expression down into parts

### Not

Let's look at the most simplest case. Not.

| a     | !a    |
| ----- | ----- |
| true  | false |
| false | true  |

### AND

| a     | b     | a && b |
| ----- | ----- | ------ |
| true  | true  | true   |
| true  | false | false  |
| false | true  | false  |
| false | false | false  |

Notice here that `a && b` is only true when both `a` and `b` are true.

### OR

| a     | b     | a \|\| b |
| ----- | ----- | -------- |
| true  | true  | true     |
| true  | false | true     |
| false | true  | true     |
| false | false | false    |

Notice here that `a || b` is only false when both `a` and `b` are false.

## Precedence (Order of Operations)

|                                   |                     |
| --------------------------------- | ------------------- |
| Parenthesis                       | `()`                |
| Logical Not                       | `!`                 |
| Arithmetic Operators              | `*` `/` `%` `+` `-` |
| Relational Operators              | `<` `<=` `>` `>=`   |
| Equality and Inequality operators | `==` `!=`           |
| Logical AND                       | `&&`                |
| Logical OR                        | `||`                |



## Playing with Truth Tables Example

### a && !b

| a     | b     | !b    | a && !b |
| ----- | ----- | ----- | ------- |
| true  | true  | false | false   |
| true  | false | true  | true    |
| false | true  | false | false   |
| false | false | true  | false   |

### !a || b

| a     | b     | !a    | !a \|\| b |
| ----- | ----- | ----- | --------- |
| true  | true  | false | true      |
| true  | false | false | false     |
| false | true  | true  | true      |
| false | false | true  | true      |

### !(a || b && c)

| a     | b     | c     | b && c | a \|\| (b && c) | !(a \|\| b && c) |
| ----- | ----- | ----- | ------ | --------------- | ---------------- |
| true  | true  | true  | true   | true            | false            |
| true  | true  | false | false  | true            | false            |
| true  | false | true  | false  | true            | false            |
| false | true  | true  | true   | true            | false            |
| true  | true  | false | false  | true            | false            |
| true  | false | true  | false  | true            | false            |
| false | true  | true  | true   | true            | false            |
| false | false | false | false  | false           | true             |

### !a || b && c

| a     | b     | c     | !a    | b && c | !a \|\| b && c |
| ----- | ----- | ----- | ----- | ------ | -------------- |
| true  | true  | true  | false | true   | true           |
| true  | true  | false | false | false  | false          |
| true  | false | true  | false | false  | false          |
| false | true  | true  | true  | true   | true           |
| true  | false | false | false | false  | false          |
| false | true  | false | true  | false  | true           |
| false | false | true  | true  | false  | true           |
| false | false | false | true  | false  | true           |

## Distributive Property of Logical Operators

The following statements are equivalent

`!(a && b)` is equivalent to  `!a || !b`

Notice how when you distribute the `!` you have to flip the operand as well. `&&` becomes `||`

Same is true for the following example

`!(a || b)` is equivalent to `!a && !b`

`!(a || b && c)` is equivalent to `!a && (!b || !c)`

## Short Circuit Evaluation

In an `&&` (AND) statement, if the left side is `false`, there is no need to evaluate the right side. Since it's going to be false anyways!!

```java
false && true; // FALSE no matter what the right side is
```

In an `||` (OR) statement, if the left side is `true, there is no need to evaluate the right side. Since it's going to be true by default!!

```java
true || false; // TRUE no matter what the right side is
```

Java takes this shortcut by default for efficiency reasons