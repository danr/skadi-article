
\section{Related Work}

One source of inspiration for this work is Leon\cite{leon},
which uses an encoding from functional programs to
uninterpreted functions in a SMT solver. Their focus is mainly
on proving properties (stated as contracts)
rather than finding counterexamples, which they see as a beneficial side effect.
Using uninterpreted
functions in a SMT solver helps to derive equivalences between values
that have not yet been fully expanded.

QuickCheck\cite{quickcheck} is an embedded DSL for finding
counterexamples for Haskell by using randomized testing.
A potential drawback of random testing is that one
has to write generators of random values suitable
for the domain. This becomes especially important in
the presence of preconditions, where the generator can
essentially become the inverse of the predicate.

One way to avoid the generator problem is to enumerate
input values for testing. This is the approach taken in
SmallCheck\cite{smallcheck} which
enumerates values on depth, and can also handle nested quantifiers.
Feat\cite{feat} instead enumerates values based on size.
Using size instead of depth as measure can sometimes be
beneficial as it grows slower, allowing for greater granularity.

By evaluating tagged undefined values (in a lazy language),
it can be observed which parts of the input are actually
demanded by the program. The forced parts of the value
can be refined with concrete values and then repeated.
This technique is called lazy narrowing, and is
used in Curry \cite{curry}, the theorem prover Agsy\cite{agsy}, and the systems Reach\cite{reach} and Lazy SmallCheck\cite{lazysc}.
The backtracking
techniques to stop exploring an unfruitful path
varies between different systems. Reach has two
modes, limiting the search space by predetermined
depth either of the input values or the function call recursion.
LazySmallCheck combines the ideas from SmallCheck and Reach to do lazy narrowing
on the depth of the values as a DSL in Haskell.

%Liquid types. (and other contracts checkers)

%EasyCheck (Curry enumeration)

%Catch
