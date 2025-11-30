---
title: "Is this program safe? Lessons from Type Theory"
date: 2025-05-10T09:28:07-04:00
draft: false 
tags:
  - type theory
  - type inference
math: true
medium_enabled: false
---

*This blog post is inspired from a lecture that Dr. Ana Milanova gave in her Principles of Program Analysis course.*

Consider an arbitrary computer program. When we execute it, we expect that it will produce some result and not get *stuck*.

For example,

```python
id = lambda x: x
id 5
```

In the code above, we create an identity function `id` which takes an argument `x` and returns that same argument. Therefore, in the second line when we call the function with the value `5`, we receive the value `5` as a result.

Now what about the following?

```python
5 id
```

This program does not make any sense since the value `5` is not a function and hence does not take anything as an argument. Ideally, we want to catch errors like these before we run our code. In fact, we can by relying on a *type checker*.

Through this, we only execute programs that have a valid *type*. If not, then we say that the program is invalid.

- `id 5` is of type `int`
- `5 id` does not have a valid type

We won't delve into the formal theory of type systems, however, know that we can design a type system to be as complicated as we'd like. We can even go as far as verifying whether the result equals an expected value at the end of program execution. However, the [Halting problem](https://en.wikipedia.org/wiki/Halting_problem) from theoretical computer science tells us that we cannot write an algorithm that's guaranteed to eventually end and tell us whether an inputted program will return a specific result.

Due to this, we need to make some compromises in type checkers. We really want it so that if a program passes the type checker, then it will never get stuck during execution by encountering something like `5 id`. Therefore, instead we compromise by failing programs that will actually never get stuck.

*Designing a type system is a trade off between runtime and how many valid programs we are able to call type safe.*

In other words, there will be programs that are valid and produce a result, however our type system will not accept it.

{{<unsafe>}}

<img alt="Venn Diagram showing that type accepted programs are smaller and within the space of valid programs" src="/files/images/blog/type-safety-venn.svg" width="500px"/>

{{</unsafe>}}

For example, let us consider one of the simplest type systems. That is the simply typed lambda calculus. We won't go into the formal details of its presentation, but instead highlight how it won't allow all valid programs through an example.

```python
id = lambda x : x
if (id true) then (id 5) else (id 6)
```

Consider again our identity function but this time it is used within an if-then-else (ite) expression. When we run this code, it will return the value `5` which is of type `int`. However, what does the type checker think?

In the simply typed lambda calculus, the type of an expression may either be a base type like an `int` or ` bool`, or it can be a function type which takes a type and returns a type (i.e,`type` $\rightarrow$ `type`).

From the definition of `id`, we cannot determine what type it has. Instead we know that for some type variable $t$, it is $t \rightarrow  t$.

Then, we take a look at the conditional part of the ite expression. We derive that `id` must have type `bool` $\rightarrow$ `bool`. However, the other two parts of the ite expression requires that `id` takes and returns an `int`!

Since `bool` and `int` are two distinct types, a type checker based on the simply typed lambda calculus will not accept this program.

In order for our type checker to accept this program, the underlying type system must support polymorphic types (sometimes called polytypes). An example system that does is System F. 

The biggest difference during type inference, is that instead of determining that `id` has type $t \rightarrow t$ for some type variable $t$. It has type $\forall t, t \rightarrow t$. Thus, allowing for both an identity function that takes a `bool` and returns a `bool`, and for an identity function to take an `int` and return an `int`.

Even with polytypes, our type checker will still not accept all valid programs! A great overview on the different dimensions of type systems is on the Wikipedia page for [Lambda Cube](https://en.wikipedia.org/wiki/Lambda_cube).

In our examples above, we had our type checker also perform inference to identify what the type of the expressions are. However, we can use more efficient algorithms if we forced the writer of the program to annotate the types instead. This is another trade off to think about when designing a programming language. 

{{<unsafe>}}

<img alt="Venn Diagram showing that simply type accepted programs are smaller and within system f accepted programs which are within space of valid programs" src="/files/images/blog/type-safety-simply-systemf-venn.svg" width="500px"/>

{{</unsafe>}}

Or, we can throw all caution to the wind and have our program crash and throw exceptions instead.

Example in Python:

```python
5 (lambda x: x)
```

```
Traceback (most recent call last):
  File "<stdin>", line 1, in <module>
TypeError: 'int' object is not callable
```

