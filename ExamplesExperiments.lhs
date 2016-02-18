\section{Examples and Experiments}
\label{examples}

In this section we aim to describe how our system works in practice by
looking at some examples. All experiments were run on
a laptop with a Intel Xeon E3-1200 processor.

\subsection{Generating sorted lists}

Assume that we are given a predicate about unique and sorted lists,
that all elements are pairwise larger than the next:
\begin{code}
usorted  ::  [Nat] -> Bool
usorted (x:y:xs)  =  x < y && usorted (y:xs)
usorted _         =  True
\end{code}
\noindent
Now we can investigate the expansion strategy based on the assumption conflict set, by asking for |xs|
such that |usorted xs| and |length xs > n|, given some bound |n|.
Our tool can output a trace showing how the incremental values
have been expanded so far.  With |n=2|, the trace looks like this:
\begin{verbatim}
xs: _
xs: Lst__
xs: Lst_(Lst__)
xs: Lst_(Lst_(Lst__))
xs: Lst_(Lst_(Lst_(Lst__)))
xs: Lst_(Lst(Nat_)(Lst_(Lst__)))
xs: Lst_(Lst(Nat_)(Lst(Nat_)(Lst__)))
xs: Lst(Nat_)(Lst(Nat_)(Lst(Nat_)(Lst__)))
xs: Lst(Nat_)(Lst(Nat(Nat_))(Lst(Nat_)(Lst__)))
xs: Lst(Nat_)(Lst(Nat(Nat_))(Lst(Nat(Nat_))(Lst__)))
xs= [Z,S Z,S (S Delayed_Nat)]
\end{verbatim}
All but the last lines describe a partial view of the value.
Delayed values are represented with a @_@, and other values
with their type constructor and the arguments. The
value @xs@ is first expanded to contain sufficiently many
elements, namely three, and
then the natural numbers start to be expanded. Note that
in this case only the necessary values are evaluated.
This can in general not be guaranteed.

The same expansion behaviour happens also when increasing
the list length, |n|. The run time is also low, generating
a sorted list of length at least 25 takes a little less than
a second, and the list |[0..24]| is indeed obtained.

% Can also generate reverese and qrev lists, can generate
% sorted lists with |sort xs=xs|.... Later we will look at the more difficult
% |sort xs=sort ys|. Sorting stuff

\subsubsection{Terminating without counterexample}

Sometimes it can be noticed that there is no counterexample regardless how the
program is expanded.  The simplest property when this happens is perhaps asking
for an |x| such that |x < Z|. The standard definition of |(<)| returns |False|
for any |y < Z|, so there is a contradiction in this context. This is also the
same context that the incremental value in |x| is waiting for, but since this is
unsatisfiable, it will never be expanded.

Let's return to the previous example with asking for an |xs|, such that
|usorted xs| and |length xs > n|, but with  the new constraint that |all (< n)
xs|.  So the list must be sorted, but the upper bounds on the data are only
local: namely that each element should be below |n|. We do not give an upper bound on the length of the list.
The other constraint is a lower bound on the list: that it should at least have length |n|.

When executing this, first the |length| constraint forces the program to expand
to make the list at least that long.  Then the |unsorted| predicate will make
sure that all the elements are pairwise ordered. This will make the first
element to be at least |Z|, the one after that at least |S Z| and so un until
the |n|th element. But then we will eventually enter the situation outlined
above and the |n|th element cannot expand any more, and the system terminates
cleanly with saying:
\begin{verbatim}
Contradiction!
No value found.
\end{verbatim}
\noindent
and thus efficiently proving the property (for a specific choice of |n|, not for all |n|.) This is perhaps surprising, because no explicit upper bound on the length of the list was given.

We can use boolean predicates in general to give all kinds of bounds on inputs, for instance depth. If the predicates bound the input sufficiently much, the tool is guaranteed to terminate.

% \subsubsection{Limitations of termination discovery}
%
% Our system is not an inductive prover and will not terminate on
%
% \begin{code}
% nub xs = y:y:ys
% \end{code}
%
% \noindent
% (Note that it does not help even if the element type is finite.)
%
% nor on:
%
% \begin{code}
% usorted (rev xs) && all (< n) xs && length xs > n
% \end{code}
%
% \noindent
% it keeps expanding the tail of the list, hoping for something....
%
% \subsubsection{Discussion about contracts checking a'la Leon}
%
% ....

\subsection{Merging the calls in merge}
\label{merge}










% The section discusses some optimisations that can be done
% to functions with more that one recursive call.
% The topic is this implementation of merge sort:
%
% \begin{code}
% msort      :: [Nat] -> [Nat]
% msort []   = []
% msort [x]  = [x]
% msort xs   = merge (msort (evens xs)) (msort (odds xs))
%
% Here, |evens, odds :: [Nat] -> [Nat]| picks ut the elements
% at the even and the odd positions, respectively.


This example about the function |merge| from merge sort aims to highlight how important
merging of function calls can be. We use
the following standard definition of |merge| that merges two lists,
returning a sorted list of the inputs:
\begin{code}
merge :: [Nat] -> [Nat] -> [Nat]
merge []      ys      = ys
merge xs      []      = xs
merge (x:xs)  (y:ys)  | x <= y     = x:merge xs (y:ys)
                      | otherwise  = y:merge (x:xs) ys
\end{code}
Evaluating merge on symbolic lists is expensive since |merge|
performs two recursive calls, leading to an exponential behaviour.
One first observation
of the situation reveals that evaluating this expression:

> merge [x_1, x_2, ..., x_n] [y_1, y_2, ..., y_m]

makes these two calls:

> merge [x_1, x_2, ..., x_n]  [y_2, ..., y_m]
> merge [x_2, ..., x_n]       [y_1, y_2, ..., y_m]

However, both of these will make the following call:

> merge [x_2, ..., x_n] [y_2, ..., y_m]

We can avoid to twice calculate this, by
memoizing the function |merge|. This leads to quadratic behavior of the symbolic evaluator.

Another observation is that the two recursive calls in |merge|
can be merged into one:
\begin{code}
merge' :: [Nat] -> [Nat] -> [Nat]
merge' []      ys      = ys
merge' xs      []      = xs
merge' (x:xs)  (y:ys)  | x <= y     = x:(merge' xs (y:ys))@1
                       | otherwise  = y:(merge' (x:xs) ys)@1
\end{code}
After merging those two function calls, the function |merge'| will make a
\emph{linear} number of calls instead of \emph{quadratic} for the memoized version, and
\emph{exponential} for the unmemoized version.

We experimentally evaluated the performance of these three versions
(without any optimizations, with memoization, and with merged calls)
by increasing a length bound |n|, and asking to find |xs|, |ys| satisfying:

> xs /= ys && msort xs == msort ys && length xs >= n

In words: two different lists that are permutations of each other,
via a |msort| function that calls the different versions of |merge|.

The results are in Figure \ref{inj}. The merged function is
significantly better: allowing to go up to lists over size 20 within
reasonable time instead of size 10. We hypothesise that this is
due to the fact that we can move the exponential behavior to the
SAT solver rather than in the size of the SAT problem.

The memoized version performs slightly better than the unmemoized
one. We also compare our runtimes to Leon\cite{leon} and LazySmallCheck\cite{lazysc}.

% The runtime is considerably better for the |merge'| version, and the memoised
% version of |merge| is considerably better than the unmemoised version.
% The runtimes are compared to Leon and LazySmallCheck.

% We also applied the |merge| to |merge'| transformation
% by hand for them, but this did not improve their runtime.

\begin{figure} \centering{
\includegraphics[scale=0.60]{inj.pdf}}
\caption{
Run time to find |xs|, |ys| such that |xs /= ys|
and |msort xs == msort ys| with a |length| constraint on |xs|.
We compare our tool with different settings (\emph{merged}, \emph{memo}, \emph{unopt})
as described in Section \ref{merge}.
and with LazySmallCheck\cite{lazysc} and Leon\cite{leon}.
\label{inj}
}
\end{figure}

The original |merge| function is structurally recursive,
but this property is destroyed when symbolically
merging to |merge'|. The symbolic values that are
fed to the recursive calls are not smaller: for instance,
the first one is |if x <= y then xs else x:xs| which
is as big as the input |x:xs|. We overcome this
introduced non-termination by introducing a |postpone|
as described in Section \ref{postpone}.

\subsection{Expressions from a type checker}




We will here consider a standard type-checker for
simply typed lambda calculus. It answers whether
a given expression has a given type, in an environment:

> tc :: [Type] -> Expr -> Type -> Bool
> tc  env  (App f x tx)  t           = tc env f (tx :-> t) && tc env x tx
> tc  env  (Lam e)       (tx :-> t)  = tc (tx:env) e t
> tc  env  (Lam e)       _           = False
> tc  env  (Var x)       t           =  case env `index` x of
>                                         Just tx  -> tx == t
>                                         Nothing  -> False

By inverting this function, we can use it
to infer the type of a given expression,
or even synthesise programs of a given type!
For instance, we can get the S combinator
by asking for an |e| such that:

> tc [] e ((A :-> B :-> C) :-> (A :-> B) :-> A :-> C)

Upon which our tool answers this term, when pretty-printed:
\begin{code}
\x y z -> ((((\v w -> w) z) x) z) (y z)
\end{code}
This takes about 7 seconds, but as can be seen above,
it contains redexes. Interestingly, we can
avoid getting redexes \emph{and} reduce the search space by
by adding a recursive predicate
|nf :: Expr -> Bool|
that checks that there is no unreduced
lambda in the expression. Now, we ask
for the same as above, and that |nf e|.
With this modification, finding the s combinator,
in normal form, takes less a fraction of a second.
Comparison with and without normal form and
with LazySmallCheck can be found in Table \ref{typetable}\footnote{We also ran Leon on this example but it timed out.}.

Constraining the data in this way allows
cutting away big parts of the search space (only normal
forms). The context where the expression is not in normal
form will become inconsistent due to the predicate,
and no delayed computations are evaluated from inconsistent
contexts. This would not be the case if we up from decided on how
big our symbolic values were. So here we see a direct benefit from
incrementally expanding the program.

Both the code for the type checker and the
normal form predicate contains calls that
can be merged in the fashion as the merge
sort. Without merging these calls, finding the normal
form of the S combinator takes about a second,
and 30 seconds without the normal form predicate.

\begin{table}
\begin{center}
\textit{
\begin{tabular}{l r r}
\em Type & \em Our & \em LazySC \\
\hline
|w    ::(a->a->b)->a->b|         & 1.0s &  - \\
|(.)  ::(b->c)->(a->b)->a->c|    & 6.7s &  - \\
|s    ::(a->b->c)->(a->b)->a->c| & 7.6s &  - \\
|w| in normal form   & $<$0.1s &     0.9s \\
|(.)| in normal form   & $<$0.1s &  - \\
|s| in normal form    & 0.1s &  - \\
\end{tabular}
}
\end{center}
\caption{Using the type checker to synthesise
expressions. LazySmallCheck was given a 300s
time limit for each depth 6, 7 and 8, timeout
is denoted with -.
}
\label{typetable}
\end{table}%

% \begin{code}
% data Expr = App Expr Expr Type | Lam Expr | Var Nat
%
% data Type = Type :-> Type | A | B | C
% tc  env  (App f x tx)  t           = tc env f (tx :-> t)
%                                    && tc env x tx
% tc  env  (Lam e)       (tx :-> t)  = tc (tx:env) e t
% tc  env  (Lam e)       _           = False
% tc  env  (Var x)       t           =  case env `index` x of
%                                         Just tx  -> tx == t
%                                         Nothing  -> False
% \end{code}
%
% \begin{code}
% nf :: Expr -> Bool
% nf (App (Lam _) _ _) = False
% nf (App f x _)       = nf f && nf x
% nf (Lam e)           = nf e
% nf (Var _)           = True
% \end{code}

\subsection{Regular expressions}
\label{regexp}













We used a regular expression library
to falsify some plausible looking laws. The library has the following api:

% We will call the main one |prop_repeat|:
%
% > Meps `notElem` p && s `elem` repp p i j & repp p i' j' ==> s `elem` repp p (maxx i i') (minn j j')
%
% Here, |repp p i j| means repeat the regular expression |p| from |i| to |j| times.
% If |i > j|, then this regular expression does not recognize any string.
% Conjunction of regular expressions is denoted by |&|.
%
% This property is false for |i = 0|, |j = 1|, |i' = j' = 2|, |p = a+aa| and |s = aa|,
% since |reppp (a+aa) (maxx 0 2) (minn 1 2) = reppp (a+aa) 2 1 = Mempset|.


> data RE a  = a :>: a  | a :+: a  | a :&: a
>            | Star a   | Eps      | Nil       | Atom Token

> step  ::  RE -> Token -> RE
> eps   ::  RE -> Bool
> rec   ::  RE -> [Token] -> Bool
> rep   ::  RE -> Nat -> Nat -> RE

The |step| function does Brzozowski differentiation, |eps|
answers if the expression contains the empty string, |rec|
answers if the word is recognised, and |rep p i j|
repeats a regular expression sequentially from |i| to |j| times.

We can now ask our system for variables satisfying:

> prop_repeat:  not (eps p) &&
>               rec s (rep p i j :&: rep p i' j') &&
>               not (rec (rep p (max i i') (min j j')) s)

whereupon we get the following counterexample in about 30 seconds:

% p:  (R(R(R__(T))(R__(T))(T))(R__(T))(T))
% i:  (Nat(Nat(Nat_)))
% i': (Nat(Nat(Nat_)))
% j:  (Nat(Nat(Nat_)))
% j': (Nat(Nat(Nat_)))
% s:  (List(T)(List(T)(List(T)_)))

\begin{verbatim}
p:  (Atom A :>: Atom A) :+: Atom A
i:  S (S Z)
i': S Z
j:  S (S Z)
j': S Z
s:  [A,A]
\end{verbatim}

This is a counterexample since
|rep p (max i i') (min j j')| = |rep p 2 1|, which recognizes
no string, but |rep p [A,A]| does hold.

We list our and LazySmallCheck's run times on
|prop_repeat| above and on two seemingly simpler
properties, namely:
\begin{code}
prop_conj:  not (eps p) && rec (p :&: (p :>: p)) s
prop_iter:  i /= j && not (eps p) && rec (iter i p :&: iter j p) s
\end{code}
The last property uses a function |iter :: Nat -> RE -> RE| which
repeats a regular expression a given number of times. The results are found
in Table \ref{regexptable}.
\begin{table}[]
\begin{center}
\textit{
\begin{tabular}{l r r }
\em Conjecture & \em Our tool & \em LazySC \\
\hline
|prop_conj|   & 27.2s &  0.6s \\
|prop_iter|   &  6.6s & 17.4s \\
|prop_repeat| & 35.7s & 103s  \\
\end{tabular}
}
\end{center}
\caption{Run times of finding counterexamples
to regular expression conjectures. The properties
are defined in Section \ref{regexp}.}
\label{regexptable}
\end{table}%
If we look more closely at the implementation of the regular expression library
we find that the calls are duplicated across the branches.
For instance, the |eps| function looks like this:
\begin{code}
eps Eps          = True
eps (p  :+:  q)  = eps p || eps q
eps (p  :&:  q)  = eps p && eps q
eps (p  :>:  q)  = eps p && eps q
eps (Star _)     = True
eps _            = False
\end{code}
Here, we could collapse all the calls |eps p| as described
in the section above, but it is actually enough to just
memoize them as they are exactly the same. (The same holds for |eps q|).
The recursive call structure of the |step| function follows
the same pattern as for |eps| and memoization is enough there as well.

% \begin{code}
% step  :: RE Token -> Token -> RE Token
% step  (Atom a)   x  = if a == x then Eps else Nil
% step  (p :+: q)  x  =  step p x :+:  step q x
% step  (p :&: q)  x  =  step p x :&:  step q x
% step  (p :>: q)  x  =  (step p x :>: q) :+:
%                        if eps p then step q x else Nil
% step  (Star p)   x  =  step p x :>: Star p
% step  _          x  = Nil
% \end{code}
%
% The previous code uses the predicate |eps :: R a -> Bool|
% which answers if a regular expression recognizes
% the empty string. We can now define the recognizer |rec|
% for an input word:
%
% \begin{code}
% rec :: RE Token -> [Token] -> Bool
% rec p []      = eps p
% rec p (x:xs)  = rec (step p x) xs
% \end{code}
%
% The first example we look at is
% relating conjunction of regular expressions |(:&:)|
% and sequential composition |(:>:)|:
%
% > not (eps p) && rec (p :&: (p :>: p)) s
%
% On this example, we get a counterexample after 28
% seconds, having explored the right part of the
% expression, but the list a little too far:
%
% \begin{verbatim}
% p: (R(R(R__(T))_(T))(R__(T))(T))
% s: (List(T)(List(T)(List(T)(List(T)_))))
%
% Counterexample!
% p: Star (Atom B) :>: Atom B
% s: Cons B (Cons B Nil)
% \end{verbatim}
%
% The second  property we looked at
% involves iterates a regular expression
% with |iter| a number of times:
%
% \begin{code}
% iter :: Nat -> R a -> R a
% iter Z     _ = Eps
% iter (S n) r = r :>: iter n r
% \end{code}
%
% The property is now is trying to find such an expression
% |p|, a word |s| and two numbers |i| and |j| such that:
%
% > i /= j && not (eps p) && rec (iter i p :&: iter j p) s
%
% On this example we explore this:
%
% \begin{verbatim}
% i: (Nat(Nat(Nat_)))
% j: (Nat(Nat(Nat_)))
% p: (R(R(R__(T))_(T))(R__(T))(T))
% s: (List(T)(List(T)(List(T)_)))
%
% Counterexample!
% i: S (S Z)
% j: S Z
% p: Star (Atom A) :>: Atom A
% s: Cons A (Cons A Nil)
% \end{verbatim}
%
% Given this:
%
% \begin{code}
% subtract1 :: Nat -> Nat
% subtract1 Z      = Z
% subtract1 (S x)  = x
%
% rep :: R T -> Nat -> Nat -> R T
% rep p i      (S j)  = (cond (isZero i) :+: p)
%                     :>: rep p (subtract1 i) j
% rep p Z      Z      = Eps
% rep p (S _)  Z      = Nil
% \end{code}
%
% Prove this:
%
% > not (eps p)  && rec (rep p i j :&: rep p i' j') s
% >              && not (rec (rep p (i `max` i') (j `min` j')))
%
% This is what we get:
%
% \begin{verbatim}
% p8: (R(R(R__(T))(R__(T))(T))(R__(T))(T))
% i0: (Nat(Nat(Nat_)))
% i': (Nat(Nat(Nat_)))
% j0: (Nat(Nat(Nat_)))
% j': (Nat(Nat(Nat_)))
% s: (List(T)(List(T)(List(T)_)))
%
% == Try solve with 74 waits ==
% Counterexample!
% p8: (Atom A :>: Atom A) :+: Atom A
% i0: S (S Z)
% i': S Z
% j0: S (S Z)
% j': S Z
% s: Cons A (Cons A Nil)
% \end{verbatim}

% \subsection{Ambiguity detection}
%
% Showing stuff, inverse.
%
% \subsection{Integration from Differentiation}
% Deriving expressions, inverse.

\subsection{Synthesising Turing machines}
\label{turing}

Another example we considered was a simulator
of Turing machines. The tape symbols are
either empty (|O|), or |A| or |B|:

> data A = O | A | B

The actions are either halting or moving
right or left and entering a new state represented with a |Nat|:

> data Action = Lft Nat | Rgt Nat | Stp

The machine is then a function from the state (a |Nat|), and
the symbol at the tape head |A|, to a symbol to be written
and a new head:

> type Q' = (Nat,A) -> (A,Action)

but we (currently) don't support functions, so we represent this
tabulated in a list instead:

> type Q      = [((Nat,A),(A,Action))]

A configuration of the machine is a state, and a zipper
of the tape head: the reversed list of the symbols to
the left, and the current symbol consed on to the symbols to the right:

> type Configuration  = (Nat,[A],[A])

The |step| function advances the machine one step, which
either terminates with the final tape, or
ends up in a  new configuration.

> step :: Q -> Configuration -> Either [A] Configuration

The |steps| function runs |step| repeatedly
until the machine terminates.

> steps  :: Q -> Configuration -> [A]

This function may of course not terminate, so
the translated functions needs to insert a |postpone|,
as described above.

The entire machine can be run from a starting
tape, by stepping it from the starting state |Zero| with |run|:

> run         :: Q -> [A] -> [A]
> run q tape  = steps q (Zero,[],tape)

We used our system to find Turing machines given a list of expected inserts the first symbol on the tape into the (sorted) rest of the symbols:

> run q [A]            == [A] &&
> run q [B,A,A,A,A,B]  == [A,A,A,A,B,B]

Asking to find such a |q|, we get this result in about thirty seconds:
\begin{code}
[  ((Succ Zero,         A),  (B,  Stp)),
   ((Succ (Succ Zero),  A),  (A,  Rgt (Succ (Succ Zero)))),
   ((Zero,              B),  (A,  Rgt (Succ (Succ Zero)))),
   ((Succ (Succ Zero),  B),  (B,  Lft (Succ Zero))),
   ((Zero,              A),  (A,  Stp)) ]
\end{code}
This machine contains a loop in state two, which is enters
upon reading an inital |B| (which is replaced with an |A|).
It then uses state two to skip by all the |A|s until
it comes to a |B|, where it backtracks, and replaces
the last |A| it found with a |B|. If the tape starts with
|A| the program terminates immediately.

In the above example we found by experimentation that
it was necessary to have no less than four A in the example,
otherwise it the returned machine would "cheat" and instead
of creating a loop, just count.

In this example it is crucial to use |postpone| to
be able to handle the possibly non-terminating |steps| function.
In systems like Reach \cite{reach}, it is possible
to limit the expansion of the program on the number of unrollings
of recursive functions. Our method with |postpone| does exactly
this, but there is no need to decide beforehand how many
unrollings are needed.


% ------------------------------------------------------------------------------

% \section{Experimental evaluation}
%
% And again, there is the merge sort times.
%
% Regexp was evaluated against leon and
% lazy small check. leon timed out on all of them
%
% We evaluated the type checker against
% lazy small check with a timeout of 300s.
%
% Turing machines were evaluated...
% LSC timed out.

%
% Compare some examples against Leon.
%
% Compare some examples against Lazy SmallCheck.
%
% Compare with/without memoization and with/without merging function calls.
%
% Compare with/without conflict minimization?
%
% Show timings of the above examples.

