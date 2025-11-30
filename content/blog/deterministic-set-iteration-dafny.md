---
title: "Deterministically Iterating over a set within Dafny functions"
date: 2025-07-06T12:27:01-04:00
draft: false
tags:
    - Dafny
    - Formal methods
    - Deterministic algorithm
    - Total order
math: false
medium_enabled: false
---

Say we have a set that we want to iterate over within a pure Dafny function. For sake of example, we will look at a set of strings. In Dafny,  `var x :| condition` denotes "let us define variable x such that \[condition\]". Therefore, a first attempt at writing our function might be:

```
function iterate_helper(collection: set<string>, acc: seq<string>): seq<string>
{
    if collection == {} then acc
    else
        var x :| x in collection;
        var newAcc := acc + [x];
        var newCollection := collection - {x};
        iterate_helper(newCollection, newAcc)
}
```

The issue is that Dafny will complain with the following error message:

> to be compilable, the value of a let-such-that expression must be uniquely determined

Dafny functions must be deterministic. This means that no matter how many times we call a function with some specified input, we will always get the same output. Therefore, as the error message suggests, we need to write a condition that *uniquely* determines `x`. One way to achieve this is to specify an order as described in [Rustan's paper](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml252.pdf):

```
function iterate_helper(collection: set<string>, acc: seq<string>): seq<string>
{
    if collection == {} then acc
    else
        var x :| x in collection && forall y | y in collection :: x <= y;
        var newAcc := acc + [x];
        var newCollection := collection - {x};
        iterate_helper(newCollection, newAcc)
}
````

Unfortunately, this code will return two errors:
> cannot establish the existence of LHS values that satisfy the such-that predicate

> to be compilable, the value of a let-such-that expression must be uniquely determined

However, it's totally possible to define an ordering over strings. We'll just need to do some work to convince the verifier of this.

### Comparing two strings
Since strings in Dafny are a sequence of characters, it turns out that the `<=` relation checks whether the left side is a prefix of the right side. Therefore, there is no such thing as a *unique* minimum element, since there are incomparable elements like "a" and "b".

As such, our first step is to create a less than or equal to (`<=`) relation that induces a total order.  Consider the following function that determines the order based on the left-most character.

```function string_le(s1: string, s2: string): bool
function string_le(s1: string, s2: string): bool
    decreases |s1| + |s2|
{
    if |s1| == 0 && |s2| > 0 then
        true
    else if |s1| > 0 && |s2| == 0 then
        false
    else if |s1| == 0 && |s2| == 0 then
        true
    else
        assert(|s1| > 0);
        assert(|s2| > 0);
        var c1 := s1[0];
        var c2 := s2[0];
        if c1 < c2 then
            true
        else if c1 > c2 then
            false
        else
            string_le(s1[1..], s2[1..])
}
```

### Properties of our comparison function

From here we need to prove that our relation induces a total order. For this, we need to show that it is reflexive, total, anti-symmetric, and transitive.

Reflexivity: All strings are less than or equal to themselves
```
lemma string_le_reflexive()
    ensures forall s :: string_le(s ,s)
{
    forall s ensures string_le(s, s)
    {
        string_le_reflexive_helper(s);
    }
}

lemma string_le_reflexive_helper(s1: string)
    ensures string_le(s1, s1)
{}
```

Totality: Given two strings, one is less than or equal to the other.
```
lemma string_le_totality()
    ensures forall s1, s2 :: string_le(s1, s2) || string_le(s2, s1)
{
    forall s1, s2 ensures string_le(s1, s2) || string_le(s2, s1)
    {
        string_le_totality_helper(s1, s2);
    }
}

lemma string_le_totality_helper(s1: string, s2: string)
    ensures string_le(s1, s2) || string_le(s2, s1)
{}

```

Antisymmetric: If one string is less than or equal to another string and that other string is also less than or equal to the original string then both strings are equivalent.
```
lemma string_le_antisymmetric()
    ensures forall s1, s2 :: string_le(s1, s2) && string_le(s2, s1) ==> s1 == s2
{
    forall s1, s2 | string_le(s1, s2) && string_le(s2, s1)
    ensures s1 == s2
    {
        string_le_antisymmetric_helper(s1, s2);
    }
}

lemma string_le_antisymmetric_helper(s1: string, s2: string)
    requires string_le(s1, s2)
    requires string_le(s2, s1)
    ensures s1 == s2
{}
```

Transitive: If one string is less than or equal to another string, and that other string is less than or equal to some third string, then the first string is less than or equal to that third string.
```
lemma string_le_transitive()
    ensures forall s1, s2, s3 :: string_le(s1, s2) && string_le(s2, s3) ==> string_le(s1, s3)
{
    forall s1, s2, s3 | string_le(s1, s2) && string_le(s2, s3)
    ensures string_le(s1, s3)
    {
        string_le_transitive_helper(s1, s2, s3);
    }
}

lemma string_le_transitive_helper(s1: string, s2: string, s3: string)
    requires string_le(s1, s2)
    requires string_le(s2, s3)
    ensures string_le(s1, s3)
{}
```

Then, we conviniently package all the properties together:
```
lemma string_le_properties()
    ensures forall s :: string_le(s, s)
    ensures forall s1, s2 :: string_le(s1, s2) && string_le(s2, s1) ==> s1 == s2
    ensures forall s1, s2, s3 :: string_le(s1, s2) && string_le(s2, s3) ==> string_le(s1, s3)
    ensures forall s1, s2 :: string_le(s1, s2) || string_le(s2, s1)
{
    string_le_reflexive();
    string_le_antisymmetric();
    string_le_transitive();
    string_le_totality();
}
```

### String sets have a minimum

With the total ordering of strings, we can prove that a smallest element exists within a non-empty set `s`. First, let us invoke our comparison properties lemma, so the verifier has access to those properties:
```
string_le_properties();
```

Since our set is non-empty, we can grab an arbitrary element from `s`.
```
var x :| x in s;
```

For this proof, we'll approach it inductively. First, let's consider when `s == {x}`.
1. By construction, every element in `s` is equal to `x`.
2. Then by reflexivity, `x` is smaller than every element in `s`.
```
assert forall y :: y in s ==> y == x;
assert forall y :: y in s ==> string_le(x, y);
```

Now let's consider the inductive case. The set in this case has more elements than just `x`. Let's consider `s'` the subset of `s` without the element `x`.
```
var s' := s - {x};
assert s' != {};
```

Since `s'` is non-empty, we can by induction say that  `s'` has a smallest element.
```
string_smallest_exists(s');
var x' :| x' in s' && forall y :: y in s' ==> string_le(x', y);
```

As `s'` is the subset of `s` without `x`, we can assert that `x'` and `x` are not the same:
```
assert x' != x;
```

From here, we compare both `x` and `x'` (which we're able to do since `<=` is total)

Case 1: `x <= x'`: By transitivity, `x` will be less than all the elements of `s'`. Since `s'` is  `s`  without `x`, we can safely say that `x` is less than every element in `s`.
```
assert forall y :: y in s' ==> string_le(x, y);
assert forall y :: y in s ==> string_le(x, y);
```

Case 2: `!(x <= x')`. From totality, we have that `x' <= x`. Since we know from the inductive hypothesis that `x'` is the minimum of `s'` and `s` is `s'` with the element `x`, we can conclude that `x'` is the smallest element of `s`.
```
assert !string_le(x, x');
assert string_le(x', x);
assert forall y :: y in s ==> string_le(x', y);
```

With that, we've proven that a smallest string exists! Here's the lemma in its entirety:

```
lemma string_smallest_exists(s: set<string>)
    requires s != {}
    decreases s
    ensures exists x :: x in s && forall y :: y in s ==> string_le(x, y)
{
    string_le_properties();

    var x :| x in s;

    // Base Case
    if s == {x} {
        assert forall y :: y in s ==> y == x;
        assert forall y :: y in s ==> string_le(x, y);
	
    // Inductive Case
    } else {
        var s' := s - {x};
        assert s' != {};
        string_smallest_exists(s');
        var x' :| x' in s' && forall y :: y in s' ==> string_le(x', y);
        assert x != x';

        if string_le(x, x') {
            assert forall y :: y in s' ==> string_le(x, y);
            assert forall y :: y in s ==> string_le(x, y);
        } else {
            // x' is smaller than x
            assert !string_le(x, x');
            assert string_le(x', x);
            assert forall y :: y in s ==> string_le(x', y);
        }
    }
}

```

### Select the smallest element from a set
Now that we have determined that a minimum exists in a set, we can use these lemmas to establish that we can uniquely determine the element that we select based on the ordering.

```
function select_string_from_set(collection: set<string>): string
    requires collection != {}
{
    string_le_properties();
    string_smallest_exists(collection);
    var value :| value in collection && forall y | y in collection :: string_le(value, y);
    value
}
```

### Conclusion

Revisiting our iteration example, we can use our new `select_string_from_set` function to iterate over a set of strings in a pure deterministic function. More specifically, we'll visit all the elements in the collection in the order defined by our relation.

```
function iterate_helper(collection: set<string>, acc: seq<string>): seq<string>
    decreases collection
{
    if collection == {} then acc
    else
        var x := select_string_from_set(collection);
        var newAcc := acc + [x];
        var newCollection := collection - {x};
        iterate_helper(newCollection, newAcc)
}
```

From here you can generalize beyond a set of strings, as long as you're able to prove the properties of a total order. The full code for our string sets example is below:


```
function string_le(s1: string, s2: string): bool
    decreases |s1| + |s2|
{
    if |s1| == 0 && |s2| > 0 then
        true
    else if |s1| > 0 && |s2| == 0 then
        false
    else if |s1| == 0 && |s2| == 0 then
        true
    else
        assert(|s1| > 0);
        assert(|s2| > 0);
        var c1 := s1[0];
        var c2 := s2[0];
        if c1 < c2 then
            true
        else if c1 > c2 then
            false
        else
            string_le(s1[1..], s2[1..])
}

lemma string_le_reflexive()
    ensures forall s :: string_le(s ,s)
{
    forall s ensures string_le(s, s)
    {
        string_le_reflexive_helper(s);
    }
}

lemma string_le_reflexive_helper(s1: string)
    ensures string_le(s1, s1)
{}

lemma string_le_totality()
    ensures forall s1, s2 :: string_le(s1, s2) || string_le(s2, s1)
{
    forall s1, s2 ensures string_le(s1, s2) || string_le(s2, s1)
    {
        string_le_totality_helper(s1, s2);
    }
}

lemma string_le_totality_helper(s1: string, s2: string)
    ensures string_le(s1, s2) || string_le(s2, s1)
{}

lemma string_le_antisymmetric()
    ensures forall s1, s2 :: string_le(s1, s2) && string_le(s2, s1) ==> s1 == s2
{
    forall s1, s2 | string_le(s1, s2) && string_le(s2, s1)
    ensures s1 == s2
    {
        string_le_antisymmetric_helper(s1, s2);
    }
}

lemma string_le_antisymmetric_helper(s1: string, s2: string)
    requires string_le(s1, s2)
    requires string_le(s2, s1)
    ensures s1 == s2
{}


lemma string_le_transitive()
    ensures forall s1, s2, s3 :: string_le(s1, s2) && string_le(s2, s3) ==> string_le(s1, s3)
{
    forall s1, s2, s3 | string_le(s1, s2) && string_le(s2, s3)
    ensures string_le(s1, s3)
    {
        string_le_transitive_helper(s1, s2, s3);
    }
}

lemma string_le_transitive_helper(s1: string, s2: string, s3: string)
    requires string_le(s1, s2)
    requires string_le(s2, s3)
    ensures string_le(s1, s3)
{}

lemma string_le_properties()
    ensures forall s :: string_le(s, s)
    ensures forall s1, s2 :: string_le(s1, s2) && string_le(s2, s1) ==> s1 == s2
    ensures forall s1, s2, s3 :: string_le(s1, s2) && string_le(s2, s3) ==> string_le(s1, s3)
    ensures forall s1, s2 :: string_le(s1, s2) || string_le(s2, s1)
{
    string_le_reflexive();
    string_le_antisymmetric();
    string_le_transitive();
    string_le_totality();
}


lemma string_smallest_exists(s: set<string>)
    requires s != {}
    decreases s
    ensures exists x :: x in s && forall y :: y in s ==> string_le(x, y)
{
    string_le_properties();

    var x :| x in s;

    if s == {x} {
        assert forall y :: y in s ==> y == x;
        assert forall y :: y in s ==> string_le(x, y);
    } else {
        // For sets with more than one element, we use induction-like reasoning
        var s' := s - {x};

        assert s' != {};
        string_smallest_exists(s');

        var x' :| x' in s' && forall y :: y in s' ==> string_le(x', y);
        assert x != x';

        if string_le(x, x') {
            assert forall y :: y in s' ==> string_le(x, y);
            assert forall y :: y in s ==> string_le(x, y);
        } else {
            // x' is smaller than x
            assert !string_le(x, x');
            assert string_le(x', x);
            assert forall y :: y in s ==> string_le(x', y);
        }
    }
}

function select_string_from_set(collection: set<string>): string
    requires collection != {}
{
    string_le_properties();
    string_smallest_exists(collection);
    var value :| value in collection && forall y | y in collection :: string_le(value, y);
    value
}

function iterate_helper(collection: set<string>, acc: seq<string>): seq<string>
    decreases collection
{
    if collection == {} then acc
    else
        var x := select_string_from_set(collection);
        var newAcc := acc + [x];
        var newCollection := collection - {x};
        iterate_helper(newCollection, newAcc)
}

```
