---
title: "Load Balancing within OpenMP Static Schedules"
date: 2023-05-05T21:42:56-04:00
draft: false 
tags: []
math: false
medium_enabled: false
---

OpenMP allows C++ developers to create shared memory multi-processing applications.
This is particularly beneficial for single program multiple data (SPMD) tasks.
However given a large batch of data to process,
it is often the case that the data cannot be evenly split among all the available parallel threads.
This creates an imbalance on how long each thread takes to finish.
One popular is to use a dynamic scheduling algorithm,
though this might not be desirable in all cases.
What if we know a unit of work that the idle threads can complete before the other threads finish?
To take advantage of this potential opportunity,
we need to understand how OpenMP distributes work within static schedules. 

Let's showcase static scheduling through an example.
Imagine we have a vector of integers from 0 to 50 and 
we wish to find the sum of this vector without using a formula.

```c++
std::vector<int> numbers(50);
std::iota(std::begin(numbers), std::end(numbers), 0);
```

Say we have eight threads.
Let's initialize the data structures that will both keep track of the sum
and keep track of the assignment of indices to each thread.

```c++
int sum = 0;
std::vector<std::unordered_set<int>> assignments(numThreads, std::unordered_set<int>());
```

In standard static scheduling, we would write the parallel portion as follows:

```c++
#pragma omp parallel for reduction(+:sum)
for (size_t i = 0; i < numbers.size(); i++)
{
    const int threadId = omp_get_thread_num();
    assignments[threadId].insert(i);
    sum += numbers[i];
}
```

If we print out the assignments vector, it would look like the following:

```
Thread ID: 0 Allocations: 06 05 04 03 02 01 00 
Thread ID: 1 Allocations: 13 12 11 10 09 08 07 
Thread ID: 2 Allocations: 19 18 17 16 15 14 
Thread ID: 3 Allocations: 25 24 23 22 21 20 
Thread ID: 4 Allocations: 31 30 29 28 27 26 
Thread ID: 5 Allocations: 37 36 35 34 33 32 
Thread ID: 6 Allocations: 43 42 41 40 39 38 
Thread ID: 7 Allocations: 49 48 47 46 45 44 
```

A couple things to notice:

- The first two threads have one extra unit of work.
This makes sense since if you divide fifty by 8 you would have two remaining.
In mathematical speak: `size % numThreads = 2`.
A generalization of the pidgeon-hole principal.

- The portions of the array that are divided are all sequential.
This is to make use of the principal of locality.
Memory locations near an access are cached as programs are more likely to access nearby locations.

To emulate this, we'll need to determine the start and end indices that each thread would consider.
To help out let's introduce two new variables.

```c++
const int leftOvers = numbers.size() % numThreads;
const int elementsPerThread = numbers.size() / numThreads;
```

The rest of this example will be within a parallel block.
Since we're not going to let OpenMP automatically distribute the work,
we'll have to specify the macro a little differently.

```c++
omp_set_dynamic(0);
omp_set_num_threads(numThreads);
#pragma omp parallel reduction(+:sum)
{
    const int threadId = omp_get_thread_num();
    // Later code is within here
}
```

The start and end indices need to take into account
not only how many elements each thread process,
but how many of the prior thread ids have an extra unit of work.

```c++
size_t start;
if (threadId > leftOvers) {
    start = (threadId * elementsPerThread) + leftOvers;
} else {
    start = threadId * elementsPerThread + threadId;
}
size_t end;
if (threadId + 1 > leftOvers) {
    end = (threadId + 1) * elementsPerThread + leftOvers;
} else {
    end = (threadId + 1) * elementsPerThread + threadId + 1;
}
```

Now we can ask each thread to iterate over their start and end indices.

```c++
for (size_t i = start; i < end; i++)
{
    assignments[threadId].insert(i);
    sum += numbers[i];
}
```

How do we know if this thread is performing less units of statically allocated work?
We check its thread id.
Since thread ids from 0 to leftOvers get assigned one more unit of work,
the thread ids that are larger than leftOvers are free game.

```c++
if (threadId > leftOvers && leftOvers > 0) {
    // Do extra work here
}
```

Now of course it's up for you to figure out what the right type of extra work is.
Since if the extra work ends up taking longer than the already allocated work, it'll remain imbalanced.
This technique, however, gives you another tool in your parallel computing toolbelt if the dynamic scheduling algorithm is suboptimal for your application.

Full load balance code example:

```c++
#include <omp.h>
#include <vector>
#include <numeric>
#include <unordered_set>
#include <iostream>
#include <iomanip>

int main ()
{     
    std::vector<int> numbers(50);
    std::iota(std::begin(numbers), std::end(numbers), 0);

    const int numThreads = 8;
    const int leftOvers = numbers.size() % numThreads;
    const int elementsPerThread = numbers.size() / numThreads;

    int sum = 0;
    std::vector<std::unordered_set<int>> assignments(numThreads, std::unordered_set<int>());

    omp_set_dynamic(0);
    omp_set_num_threads(numThreads);
    #pragma omp parallel reduction(+:sum)
    {
        const int threadId = omp_get_thread_num();
        size_t start;
        if (threadId > leftOvers) {
            start = (threadId * elementsPerThread) + leftOvers;
        } else {
            start = threadId * elementsPerThread + threadId;
        }
        size_t end;
        if (threadId + 1 > leftOvers) {
            end = (threadId + 1) * elementsPerThread + leftOvers;
        } else {
            end = (threadId + 1) * elementsPerThread + threadId + 1;
        }

        for (size_t i = start; i < end; i++)
        {
            assignments[threadId].insert(i);
            sum += numbers[i];
        }

        if (threadId > leftOvers && leftOvers > 0) {
            // Do extra work here
        }
    }

    // Print reduced sum
    std::cout << "sum = " << sum << std::endl;

    // Print thread allocations
    for (size_t i = 0; i < assignments.size(); i++)
    {
        std::cout << "Thread ID: " << i << " Allocations: ";
        for (const auto identifier : assignments[i]) {
            std::cout << std::setfill('0') << std::setw(2) <<  identifier << " ";
        }
        std::cout << std::endl;
    }

    std::cout << "Min Allocations per Thread: " << (elementsPerThread) << std::endl; 
    std::cout << "Extra: " << (leftOvers) << std::endl;

    return 0;
}
```

Note to future self, to compile an OpenMP application you need to specify it within `g++`

```bash
g++ -fopenmp filename.cpp -o executablename
```



  
