---
title: "Tail Call Optimization in Python"
date: 2020-10-11T20:46:54-04:00
draft: false
tags: []
---

In a standard recursive function, a new stack frame is created every time a recursive call is made. This can lead to bad memory performance and as a protective measure, some programming languages have a maximum stack frame limit. 

The following example is in Python:

```python
def factorial(n):
    if n == 0:
        return 1
    return n * factorial(n-1)
```

```python
>>> factorial(1000)
Traceback (most recent call last):
  File "<stdin>", line 1, in <module>
  File "<stdin>", line 4, in factorial
  File "<stdin>", line 4, in factorial
  File "<stdin>", line 4, in factorial
  [Previous line repeated 995 more times]
  File "<stdin>", line 2, in factorial
RecursionError: maximum recursion depth exceeded in comparison
```

## Implementation

To get around this in Python, we need some sort of [trampoline](https://en.wikipedia.org/wiki/Tail_call#Through_trampolining), or way to exit part the stack and call the recursive function again. This technique is often used in Tail Call Optimization, and we can do this in Python using exceptions. This code is heavily inspired by Crutcher Dunnavant's [code snippet](https://code.activestate.com/recipes/474088-tail-call-optimization-decorator/) from 2006.

```python
"""
Python Decorator that enables tail call
optimization through Exception Trampolines.
"""
from dataclasses import dataclass, field
from typing import Any, Dict, List
import functools
import inspect

@dataclass
class TailRecurseException(Exception):
    """Exception to enable tail call recursion."""
    args: List[Any] = field(default_factory=list)
    kwargs: Dict[Any, Any] = field(default_factory=dict)

def tail_call(func):
    """
    Decorator that performs tail call optimization.

    Notes
    =====
    Works by throwing an exception to exit the stack
    when the function sees itself as its grandparent in
    the stack trace. It then calls itself with its new
    arguments.
    """
    @functools.wraps(func)
    def recurse(*args, **kwargs):
        frame = inspect.currentframe()
        if frame.f_back is not None \
           and frame.f_back.f_back is not None \
           and frame.f_back.f_back.f_code == frame.f_code:
            raise TailRecurseException(args, kwargs)
        while True:
            try:
                return func(*args, **kwargs)
            except TailRecurseException as exception:
                args = exception.args
                kwargs = exception.kwargs
    return recurse

```

## Example: Factorial

Now let's redefine `factorial` in a tail-call way:

```python
@tail_call
def factorial(n, acc=1):
    if n == 0:
        return acc
    return factorial(n - 1, n * acc)
```

For the moment of truth...

```python
>>> factorial(1000)
402387260077093773543702433923003985719374864210714632543799910429938512398629020592044208486969404800479988610197196058631666872994808558901323829669944590997424504087073759918823627727188732519779505950995276120874975462497043601418278094646496291056393887437886487337119181045825783647849977012476632889835955735432513185323958463075557409114262417474349347553428646576611667797396668820291207379143853719588249808126867838374559731746136085379534524221586593201928090878297308431392844403281231558611036976801357304216168747609675871348312025478589320767169132448426236131412508780208000261683151027341827977704784635868170164365024153691398281264810213092761244896359928705114964975419909342221566832572080821333186116811553615836546984046708975602900950537616475847728421889679646244945160765353408198901385442487984959953319101723355556602139450399736280750137837615307127761926849034352625200015888535147331611702103968175921510907788019393178114194545257223865541461062892187960223838971476088506276862967146674697562911234082439208160153780889893964518263243671616762179168909779911903754031274622289988005195444414282012187361745992642956581746628302955570299024324153181617210465832036786906117260158783520751516284225540265170483304226143974286933061690897968482590125458327168226458066526769958652682272807075781391858178889652208164348344825993266043367660176999612831860788386150279465955131156552036093988180612138558600301435694527224206344631797460594682573103790084024432438465657245014402821885252470935190620929023136493273497565513958720559654228749774011413346962715422845862377387538230483865688976461927383814900140767310446640259899490222221765904339901886018566526485061799702356193897017860040811889729918311021171229845901641921068884387121855646124960798722908519296819372388642614839657382291123125024186649353143970137428531926649875337218940694281434118520158014123344828015051399694290153483077644569099073152433278288269864602789864321139083506217095002597389863554277196742822248757586765752344220207573630569498825087968928162753848863396909959826280956121450994871701244516461260379029309120889086942028510640182154399457156805941872748998094254742173582401063677404595741785160829230135358081840096996372524230560855903700624271243416909004153690105933983835777939410970027753472000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

```

## Example: Fibonacci Numbers

```python
@tail_call
def fib(n, a=0, b=1):
    if n == 0:
        return a
    if n == 1:
        return b
    return fib(n - 1, b, a + b)
```

```python
>>> fib(1000)
43466557686937456435688527675040625802564660517371780402481729089536555417949051890403879840079255169295922593080322634775209689623239873322471161642996440906533187938298969649928516003704476137795166849228875
```

## Conclusion

You can install the package via pypi:

```bash
pip install tail-recurse
```

It is also available on [Github](https://github.com/Brandon-Rozek/tail-recurse/).