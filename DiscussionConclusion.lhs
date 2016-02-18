
\section{Discussion and Future Work}

In the beginning of the paper, we made three assumptions about the language we are dealing with: (1) programs terminate, (2) programs do not crash, and (3) programs are first-order. We managed to lift restriction (1) by using |postpone|, as explained in Section \ref{postpone}. For non-terminating programs, the semantics of our language is lazy, and counter examples are sound w.r.t. partial correctness.

Restriction (2) can be lifted too, but this is not shown in the paper. We outline the procedure here: an extra constructor |Crash| is added to each data type that corresponds to a program crash. Every case should propagate this program crash constructor. This will make it possible to discover inputs that crash the program by asking for |Crash| instead of asking for |True| or |False|.

We can also lift restriction (3). We can synthesise functions by representing them as look-up tables. The Turing machine example from the previous section uses this encoding and thus shows the feasibility of this approach. Futhermore, higher-order functions can be supported in general by passing concrete closures from defunctionalising the program.

We first sketched out a translation based on \ifthenelse{} in Section \ref{ite},
but abandoned it for using |>>>| to be able to make incremental |new| (in Section \ref{dsl}).
It is our current belief after working with this for some time that it is
not possible to implement incrementality in the \ifthenelse{} setting.

In the Reach\cite{reach} setting, it is possible to annotate a target
expression. We think this is a very convenient way of specifying all kinds of properties, and
want to incorporate this feature in our tool as well.

One interesting step is to incorporate integer reasoning from SMT
solvers. We have already done this in one of our prototype implementations.
However, it is unclear what should happen when performing recursion over such integers.
Any function doing this, even if it is structurally recursive, would need to be guarded
by an occurrence of |postpone|, otherwise the constraint generation may not terminate.
Investigating how the power of other SMT theories could be leveraged, in particular those for
equality and uninterpreted functions, remains futher work.

% ------------------------------------------------------------------------------

\section{Conclusions}

We decided to tackle a hard problem (finding program inputs that lead to certain program outputs) in a new way (using a SAT-solver) and a new setting (functional programs with algebraic datatypes). The first remark we can make is that it is surprising that it can be done at all: we can generate constraints about general high-level programs, in terms of a logic for a finite number of binary choices, in a sound and complete way.

We use the conflict set of the SAT-solver to decide how to expand the input incrementally until a suitable input is found. Our experiments have shown that this actually works rather well, very often just the right constructors are chosen. We also apply memoization and function call merging to battle exponential blow-up, and have experimentally shown that both of these have a positive effect, with function call merging being vital for certain problems to even succeed.

Our method works well for cases where the generation of the SAT-problem does not blow up. It can outperform other methods in cases where one gains something from the extra combinatorial search power. The method does not work well when the input expansion chooses the wrong thing to expand, or when the expansion needs too many steps to reach the correct input shape. We have not encountered any problem that turned out to be too hard for the SAT-solver itself; most SAT calls terminate almost immediately (even for large problems), and very few calls take more than, say, a second.
