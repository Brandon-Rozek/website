---
title: Types of Programming Languages
---

Mostly content from [Wikipedia](https://en.wikipedia.org/wiki/List_of_programming_languages_by_type#Hardware_description_languages)

## Array Languages

Array programming languages generalizes operations on scalars to apply transparently to vectors, matrices, and higher-dimensional arrays.

Example Language: R

In R everything is by default a vector, typing in 

```R
x <- 5
```

Will create a vector of length 1 with the value 5.

This is commonly used by the scientific and engineering community. Other languages include MATLAB, Octave, Julia, and the NumPy extension to Python.

## Constraint Programming Languages

A declarative programming language where relationships between variables are expressed as constraints. Execution proceeds by attempting to find values for the variables that satisfy all declared constraints.

Example: Microsoft Z3 Theorem Prover

```z3
(declare-const a Int)
(declare-fun f (Int Bool) Int)
(assert (> a 10))
(assert (< (f a true) 100))
(check-sat)
```

## Command Line Interface Languages

Commonly used to control jobs or processes

```bash
#!/bin/bash
echo "hello, $USER. I wish to list some files of yours"
echo "listing files in the current directory, $PWD"
ls  # list files
```

## Concurrent Languages

Languages that support language constructs for concurrency. These may involve multi-threading, distributed computing, message passing, shared resources, and/or future and promises.

Example: Erlang

```erlang
ping(0, Pong_PID) ->
    Pong_PID ! finished,
    io:format("ping finished~n", []);

ping(N, Pong_PID) ->
    Pong_PID ! {ping, self()},
    receive
        pong ->
            io:format("Ping received pong~n", [])
    end,
    ping(N - 1, Pong_PID).

pong() ->
    receive
        finished ->
            io:format("Pong finished~n", []);
        {ping, Ping_PID} ->
            io:format("Pong received ping~n", []),
            Ping_PID ! pong,
            pong()
    end.

start() ->
    Pong_PID = spawn(tut15, pong, []),
    spawn(tut15, ping, [3, Pong_PID]).
```



## Data-oriented Languages

These languages provide powerful ways of searching and manipulating relations.

Example: SQL

```sql
SELECT * FROM STATION
WHERE 50 < (SELECT AVG(TEMP_F);
```

Give all the information from stations whose average temperature is above 50 degrees F

## Declarative Languages

Declarative languages express the logic of a computation without describing its control flow in detail

Example: SQL again

The example code above doesn't tell the computer how to perform the query, just what you want.

## Functional Languages

Style of computer programs that treat computation as the evaluation of mathematical functions and avoid changing-state and having mutable data.

```haskell
primes = filterPrime [2..] 
  where filterPrime (p:xs) = 
          p : filterPrime [x | x <- xs, x `mod` p /= 0]
```

## Imperative Languages

The use of statements to change a program's state

Example: C

```c
#define FOOSIZE 10
struct foo fooarr[FOOSIZE];

for(i = 0; i < FOOSIZE; i++)
{
  do_something(fooarr[i].data);
}
```



## Iterative Languages

Languages built around or offering generators

Example: Python

```python
def countfrom(n):
    while True:
        yield n
        n += 1
        
g = countfrom(0)
next(g) # 0
next(g) # 1
```

## List-based Languages -LISPs

Family of programming languages with a history of fully parenthesized prefix notation.

Example: Common Lisp

```commonlisp
 ;; Sorts the list using the > and < function as the relational operator.
 (sort (list 5 2 6 3 1 4) #'>)   ; Returns (6 5 4 3 2 1)
 (sort (list 5 2 6 3 1 4) #'<)   ; Returns (1 2 3 4 5 6)
```

## Logic Languages

Programming paradigm based on formal logic. Expressions are written stating the facts and rules about some problem domain.

Example: Prolog

```prolog
mother_child(trude, sally).
 
father_child(tom, sally).
father_child(tom, erica).
father_child(mike, tom).
 
sibling(X, Y)      :- parent_child(Z, X), parent_child(Z, Y).
 
parent_child(X, Y) :- father_child(X, Y).
parent_child(X, Y) :- mother_child(X, Y).
```

```prolog
?- sibling(sally, erica).
 Yes
```

## Symbolic Programming

A programming paradigm in which the program can manipulate its own formulas and program components as if they were plain data.

Example: Clojure

Clojure is written in prefix notation, but with this macro, you can write in infix notation.

```clojure
(defmacro infix
  [infixed]
  (list (second infixed) 
        (first infixed) 
        (last infixed)))
```



## Probabilistic Programming Language

Adds the ability to describe probabilistic models and then perform inference in those models.

Example: Stan

```stan
model {
	real mu;
	
	# priors:
	L_u ~ lkj_corr_cholesky(2.0);
	L_w ~ lkj_corr_cholesky(2.0);
	to_vector(z_u) ~ normal(0,1);
	to_vector(z_w) ~ normal(0,1);
	
	for (i in 1:N){
		mu = beta[1] + u[subj[i],1] + w[item[i],1] 
			+ (beta[2] + u[subj[i],2] + w[item[i],2])*so[i];
           rt[i] ~ lognormal(mu,sigma_e);        // likelihood
      }
}
```



## Quick Summary of Programming Paradigms

Imperative

- Object Oriented
- Procedural

Declarative

- Functional
- Logic

Symbolic Programming

