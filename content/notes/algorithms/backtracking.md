# Backtracking
This algorithm tries to construct a solution to a problem one piece at a time. Whenever the algorithm needs to decide between multiple alternatives to the part of the solution it *recursively* evaluates every option and chooses the best one.


## How to Win
To beat any *non-random perfect information* game you can define a Backtracking algorithm that only needs to know the following.
- A game state is good if either the current player has already won or if the current player can move to a bad state for the opposing player.
- A game state is bad if either the current player has already lost or if every available move leads to a good state for the opposing player.

```
PlayAnyGame(X, player)
  if player has already won in state X
    return GOOD
  if player has lost in state X
    return BAD
  for all legal moves X -> Y
    if PlayAnyGame(y, other player) = Bad
      return GOOD
  return BAD
```

In practice, most problems have an enormous number of states not making it possible to traverse the entire game tree.

## Subset Sum

For a given set, can you find a subset that sums to a certain value?

```
SubsetSum(X, T):
  if T = 0
    return True
  else if T < 0 or X is empty
    return False
  else
    x = any element of X
    with = SubsetSum(X \ {x}, T - x)
    without = SubsetSum(X \ {x}, T)
    return (with or without)
```

X \ {x} denotes set subtraction. It means X without x.

```
ConstructSubset(X, i, T):
  if T = 0
    return empty set
  if T < 0 or n = 0
    return None
  Y = ConstructSubset(X, i - 1, T)
  if Y does not equal None
    return Y
  Y = ConstructSubset(X, i - 1, T - X[i])
  if Y does not equal None
    return Y with X[i]
  return None
```

## Big Idea

Backtracking algorithms are used to make a *sequence of decisions*.

When we design a new recursive backtracking algorithm, we must figure out in advance what information we will need about past decisions in the middle of the algorithm.