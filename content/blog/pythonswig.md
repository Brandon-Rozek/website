---
title: "C++ within Python with SWIG"
date: 2020-10-27T23:49:54-04:00
draft: false
tags: ["Python", "C++"]
---

For performance reasons, it can be useful to write functions in C/C++ which can then be called within Python. This will be an introductory post, in where we will call a simple C++ function (with a dependency) within Python using [SWIG](http://swig.org/).

First we need to install SWIG:

```bash
sudo apt install swig
```

We're going to use [GNU MP](https://gmplib.org/) in order to have arbitrary precision arithmetic for our factorial function. 

```bash
sudo apt install libgmp-dev
```

## Source Setup

Normally people use headers for larger C++ programs, though we're going to create one just so we can see how to include it later in SWIG. Let's called this file `factorial.hpp`

```c++
#ifndef FACTORIAL_H
#define FACTORIAL_H
std::string fact(unsigned int n);
#endif
```

In order to get it the large number from C++ to Python. We are going to use `std::string` as the return of our `fact` function.

Here is the source `factorial.cpp`

```c++
#include <gmpxx.h>
#include "factorial.hpp"

std::string fact(unsigned int n) {
        if (n == 0) {
                n = 1;
        }
        mpz_class result(n);
        while (n > 1) {
                n--;
                result *= n;
        }
        return result.get_str(10); // Base 10
}

```

Now that we have our C++ code, we need to create a swig template file called `factorial.i`

```
 %module factorial
 %{
 #include "factorial.hpp"
 %}
 
 %include <std_string.i>
 %include "factorial.hpp"
 
```

Since we're returning a `std::string` we need to tell SWIG what that is. We do this through the `<std_string.i>` include.

We can now ask SWIG to write the C++ code that will interface with Python. This will create the files  `factorial_wrap.cxx` and `factorial.py`.

```bash
swig -c++ -python factorial.i
```

## Compilation and Linkage

Let's compile our C++ code.

```bash
g++ -O2 -fPIC -c factorial.cpp 
```

| Flag  | Description                                                  |
| ----- | ------------------------------------------------------------ |
| -O2   | Perform nearly all supported optimizations that don't involve a space-speed tradeoff. |
| -fPIC | Create Position-Independent Code                             |
| -c    | Don't link at this time                                      |

To compile `factorial_wrap.cxx` we need to include the directory where `Python.h` lives. You can find this by issuing the command `locate Python.h`. Below is where it is located on my system.

```bash
g++ -O2 -fPIC -c factorial_wrap.cxx -I/home/user/.pyenv/versions/3.8.2/include/python3.8/
```

Finally let's create the needed shared object file by linking `factorial.o`, `factorial_wrap.o`, and the GNU MP libraries.

```bash
g++ -O2 -fPIC -shared factorial.o factorial_wrap.o -lgmpxx -lgmp -o _factorial.so
```

It is important that our final output is called `_` + module_name.so

We should at this time be able to open up `python` and import our function.

```python
import factorial
factorial.fact(5)
```

If you run into any errors, the [SWIG Documentation](http://www.swig.org/Doc3.0/Python.html#Python_nn3) is quite helpful.

In order to not have to type out the compiling and linking commands every time, here is a  Makefile

```makefile
CC=g++
CFLAGS=-O2 -fPIC -Wall
PYTHON_PATH=/home/user/.pyenv/versions/3.8.2/include/python3.8/

all: _factorial.so

_factorial.so: factorial.o factorial_wrap.o
	$(CC) $(CFLAGS) -shared factorial.o factorial_wrap.o -lgmpxx -lgmp -o _factorial.so

factorial_wrap.o: factorial_wrap.cxx
	$(CC) $(CFLAGS) -c factorial_wrap.cxx -I$(PYTHON_PATH)

factorial.o: factorial.cpp
	$(CC) $(CFLAGS) -c factorial.cpp

factorial_wrap.cxx: factorial.i
	swig -c++ -python factorial.i

clean:
	rm *.o *.so factorial_wrap.cxx factorial.py
```

Then you can call `make clean` to clean up everything and `make` to run all the individual compilation steps we did before.