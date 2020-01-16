# Greedy Algorithms

Greedy Algorithms are about making the best local choice and then blindly plowing ahead.

An example of this is documents on a tape. Let's say to read any given document on a tape, you first need to read all the documents that come before it.

What is the best way to have the documents laid out in order to decrease the expected read time? 

Answer: Putting the smaller documents first.

The book then generalizes it further by adding access frequencies. The answer to that is to sort by increasing length first and then decreasing access times.

## Scheduling Classes
To maximize the number of classes one can take one greedy algorithm is to always select the class that ends first.

That will produce one maximal conflict free schedule.

## Structure of Correctness Proofs for Greedy Algorithms

- Assume that there is an optimal solution that is different from the greedy solution.
- Find the first "difference" between the two solutions.
- Argue that we can exchange the optimal choice for the greedy choice without making the solution worse.

## Hospital-Doctor Matching
Let's say you have a list of doctors that need internships and hospitals accepting interns. We need to make it so that every doctor has a job and every hospital has a doctor. 

Assuming we have the same number of doctors and hospitals and that each hospital offers only one internship, how do we make an algorithm to ensure that no unstable matchings exist?

An unstable match is when
- a is matched with some other hospital A even though she prefers B
- B is matched with some doctor b even though they prefer a.

The Gale-Shapley algorithm is a great greedy fit. It goes like this

1. An arbitrary unmatched hospital A offers its position to the best doctor a who has not already rejected it.
2. If a is unmatched, she tentatively accepts A's offer. If a already had a match but prefers A, she rejects her current match and tentatively accepts the new offer from A. Otherwise a rejects the new offer.