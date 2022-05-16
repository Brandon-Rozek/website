---
title: "Davis Putnam Satisfiability Algorithm"
math: false
---

The Davis Putnam (DP) algorithm is the first resolution based algorithm
created in 1960 that checks whether or not a given formula is satisfiable.
That is, there exists an assignment of propositions that can make the formula true. 

They later made a refinement of this algorithm in 1962 called the "Davis Putnam Logemann
Loveland" (DPLL). In fact, the refinement is so widely used that it is difficult to find a clear
document describing the earlier edition.
This page will attempt to describe the origial DP algorithm. To obtain the DPLL algorithm replace the
resolution rule with the splitting rule.


The core idea of the algorithm is to transform the formula to a simpler but equisatisfiable one.
This algorithm takes a list of clauses, which is considered to be in CNF.
For example for the following list of clauses: `[[a, b, c], [d, e]]`
we get the following formula `(a + b + c)(d + e)`

The algorithm has three rules associated with it:
- [Unit Propagation](#unit-propagation)
- [Affirmative-Negative](#affirmative-negative)
- [DP Resolution](#dp-resolution)
- [Conclusion](#conclusion)

## Unit Propagation

If there is a clause that only contains one literal `p` then:

1. Remove clauses containing `p`
2. Remove all instances of `Not(p)`

```python
def _unit_propagation(x: List[Clause]) -> List[Clause]:
    """
    Applies unit propagation.

    If there is a clause with one literal p then
    (1) Remove clauses containing p
    (2) Remove all instances of Not(p)
    """
    # Find all unit clauses
    single_literals = (c[0] for c in x if len(c) == 1)

    # Only focus on one this rule application as
    # [[p], [Not(p)]] is an edge case
    single_literal = next(single_literals, None)

    # If there are no unit clauses, move onto the next rule.
    if single_literal is None:
        return x

    # (1) Remove clauses containing the unit clause
    new_x = [c for c in x if all((l != single_literal for l in c))]

    # (2) Remove all instances of Not(p)
    negated_single_literal = negate(single_literal)
    new_x = [[l for l in c if l != negated_single_literal] for c in new_x]

    return new_x
```



## Affirmative-Negative

Remove clauses that contains literals that only occur positively in the list of clauses or negatively.

```python
def _affirmative_negative(x: List[Clause]) -> List[Clause]:
    """
    Remove clauses containing a literal
    that only occurs positively or negatively
    """
    literal_counts = _literal_counts(x)
    positive_literals, negative_literals = _pos_neg_lits(literal_counts)

    # Collect literals that are strictly positive or negative
    # but not both
    strict_literals = positive_literals ^ negative_literals

    # Only consider one strict literal
    strict_literal = next(iter(strict_literals), None)

    # If there are no strict literals,
    # move on to the next rule
    if strict_literal is None:
        return x

    # Remove clauses that contain the strict literal
    return [c for c in x 
        if all(
            (l != strict_literal and negate(l) != strict_literal 
                for l in c)
        )]

```





## DP Resolution

- Find a literal `p` that occurs both positively and negatively in the list of clauses.
  - As a heuristic, choosing a `p` that is the least common to minimize the state size.
- Create a list `C` containing clauses where `p` occurs positively; removing `p` from each clause.
- Create a list `D` containing clauses where `p` occurs negatively; removing `Not(p)` from each clause.
- Create a list `X` that contains clauses that do not contain `p` or `Not(p)` in them.
- Return `X + C + D` as the new list of clauses.

```python
def _dp_resolution(x: List[Clause]) -> List[Clause]:
    """
    Take a literal that occurs positvely and negatively
    and combine clauses that occur positively and
    negatively with p.
    """
    # Find literals that occur both positively and negatively
    literal_counts = _literal_counts(x)
    positive_literals, negative_literals = _pos_neg_lits(literal_counts)
    polar_literals = positive_literals & negative_literals

    # If there are no such literals, then move
    # onto the next rule.
    if len(polar_literals) == 0:
        return x

    # Count the number of occurances of each of the polar
    # literals and choose the least common literal p as
    # a heuristic.
    polar_literal_counts = dict(filter(lambda y: y[0] in polar_literals, literal_counts.items()))
    p, _ = min(polar_literal_counts.items(), key=itemgetter(1))

    # Create a list C containing clauses where p occurs
    # positively; removing p from the clause
    C = [[l for l in c if l != p] for c in x if p in c]

    # Create a list D containing clauses where p occurs
    # negatively; removing Not(p) from the clause
    D = [[l for l in c if l != negate(p)] for c in x if negate(p) in c]

    # Combine C and D
    new_x: List[Clause] = []
    for ci in C:
        for di in D:
            # Or(ci, di) removing duplicate literals
            cdi = list(set(ci + di))
            # No point in adding a clause that already exists.
            if cdi not in new_x:
                new_x.append(cdi)

    # Clauses that don't contain p or not p in it
    x0 = [c for c in x if p not in c and negate(p) not in c]

    return new_x + x0
```





## Conclusion

The complete DP algorithm is a recursive one with two base cases:
- If the length of the list of clauses is zero, then it is satisfiable
- If `[]` is in the list of clauses, then it is not satisfiable.

Then it applies the first rule that matches out of the three:
- [Unit Propagation](#unit-propagation)
- [Affirmative-Negative](#affirmative-negative)
- [DP Resolution](#dp-resolution)


```python
def davis_putnam(x: List[Clause]) -> bool:s
    """
    Davis-Putnam procedure for deciding
    satisfiability from CNF clauses.

    This is called recursively and it applies
    the first rule that matches: Unit Propagation,
    Affirmative-Negative, Resolution.
    """
    # Base Cases
    if len(x) == 0:
        return True
    if [] in x:
        return False

    # (1) Unit Propagation
    x_new = _unit_propagation(x)
    if x_new != x:
        return davis_putnam(x_new)

    # (2) Affirmative-Negative
    x_new = _affirmative_negative(x)
    if x_new != x:
        return davis_putnam(x_new)

    # (3) DP Resolution
    x_new = _dp_resolution(x)
    return davis_putnam(x_new)

```

