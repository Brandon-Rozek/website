---
title: "Conditional Assignment in Bash"
date: 2022-06-19T18:49:47-04:00
draft: false
tags: ["Bash"]
math: false
---

Many programming languages include an quick way to perform a
conditional assignment. That is, assigning a variable with a value
based on some condition. Normally this is done through a ternary
operator. For example, here is how to write it in Javascript

```javascript
age = 16;
ageType = (age > 18) "Adult": "Child";
```
The variable `ageType` is dependent upon the value of `age`. If it is above 18 then `ageType = "Adult"` otherwise `ageType = "Child"`.

A more verbose way of accomplishing the same thing is the following:
```javascript
if (age > 18) {
    ageType = "Adult"
} else {
    ageType = "Child"
}
```

How do we do conditional assignment in Bash? One way is to make use of subshells and echoing out the values.

```bash
AGE_TYPE=$([ $AGE -gt 18 ] && echo "Adult" || echo "Child")
```
A common programming feature called *short-circuiting* makes it
so that if the first condition (`[ $AGE -gt 18 ]`) is false, then it
will skip the right side of the AND (`&&`) expression. This is because
`False && True` is always `False`. However, `False || True` is equal
to `True`, so the language needs to evaluate the right part of an
OR (`||`) expression.
