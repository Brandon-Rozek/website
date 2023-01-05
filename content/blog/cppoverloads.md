---
title: "C++ Overloads"
date: 2020-03-07T13:52:05-05:00
draft: false
tags: [ "C++" ]
medium_enabled: true
---

One thing I like about a lot of common languages like C++ and Python is that you can overload operators. This makes it easy to create libraries for other developers that are easy to use. We are going to explain common operators you may want to overload in C++.

## Quick Example

Let's create a class

```c++
class DataType {
    public:
      DataType() {}
      bool operator==(const DataType&, const DataType&);
    private:
      int y;
}
```

Notice that we're going to overload the `==` operator for this DataType.

```c++
bool operator==(const DataType &x1, const DataType &x2) {
    return x1.y == x2.y;
}
```

## Common Unary Operators

| Name               | Operator        |
| ------------------ | --------------- |
| Increment          | `++`            |
| Decrement          | `--`            |
| Function Call      | `()`            |
| Boolean Conversion | `(bool)` object |

```c++
class DataType {
  public:
    DataType() {}
    // Boolean Conversion
    bool operator bool(const DataType&);
    // (In/De)crements
    DataType& operator++(DataType&);
    DataType& operator--(DataType&);
    // Function Call operator
    void operator(DataType& x)(int);
  private:
    int y;
}
```

```c++
// Boolean Conversion
bool operator bool(const DataType& x) {
    return x.y == 0;
}
// (In/De)crements
DataType& operator++(DataType& x) {
    x.y++;
    return x;
}
DataType& operator--(DataType& x) {
    x.y--;
    return x;
}
// Function Call Operator
void operator(DataType& x)(int n) { 
    x.y += n; 
}
```

## Common Binary Operators

| Name              | Operator |
| ----------------- | -------- |
| Stream Insertion  | `<<`     |
| Stream Extraction | `>>`     |
| Less than         | `<`      |
| Equals            | `==`     |
| Subscript         | `[]`     |

Implementing `<` gives you `>`,`<=`, and `>=` for free.

Implementing `==` gives you `!=` for free.

```c++
class DataType {
  public:
    DataType() {}
    DataType(int x) { y += x }
    // Stream Operators
    std::ostream& operator<<(std::ostream&, const DataType&);
    std::istream& operator>>(std::istream&, DataType&);
    // Arithmetic Operators
    DataType& operator+=(DataType&, const DataType&);
    DataType operator+(const DataType&, const DataType&);
    // Comparison Operators
    bool operator<(const DataType&, const DataType&);
    bool operator==(const DataType&, const DataType&);
    // Array Subscript
    int operator[](DataType&, std::size_t);
  private:
    int y;
}
```

```c++
// Stream Operators
std::ostream& operator<<(std::ostream& os, const DataType& x) {
    os << x.y;
    return os;
}
std::istream& operator>>(std::istream& is, DataType& x) {
    int y;
    is >> y;
    x.y = y;
    return is;
}
// Artithmetic Operators
DataType& operator+=(DataType& x, const DataType& z) {
    x.y += z.y;
    return x;
}
DataType operator+(const DataType& x, const DataType& z) {
    return DataType(x.y + z.y);
}
// Comparison Operators
bool operator<(const DataType &x, const DataType &z) {
    return x.y < z.y;
}
bool operator==(const DataType &x, const DataType &z) {
    return x.y == z.y;
}
// Array Subscript
int operator[](DataType& x, std::size_t idx) {
    return x.y;
}
```

