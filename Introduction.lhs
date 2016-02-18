\section{Introduction}

At the end of the 1990s, SAT-based Bounded Model Checking (BMC \cite{bmc}) was introduced as an alternative to BDD-based hardware model checking. BMC revolutionized the field; SAT-solvers by means of BMC provided a scalable and efficient search method for finding bugs. A BMC tool enumerates a depth bound $d$, starting from 0 upwards, and tries to find a counter example of length $d$, using a SAT-solver. Deep bug finding was one thing BDD-based methods were not good at. Since then, BMC techniques have also found their way into software model checkers. One example is the C model checker CBMC \cite{cbmc}. BMC techniques work well for software that is low-level (reasoning about bits, words, and arrays), and not well at all for software with higher-level features (pointers, recursive datastructures).

Our aim in this paper is to take the first step towards bringing the power of SAT-based BMC to a high-level functional programming language, with algebraic datatypes and recursion. The goal is to provide a tool that can find inputs to programs that result in outputs with certain properties. Applications include property testing, finding solutions to search problems which are expressed as a predicate in a functional language, inverting functions in a program, finding test data that satisfies certain constraints, etc.

There exist alternatives to using a SAT-solver for these problems. For example, QuickCheck \cite{quickcheck} is a tool for random property-based testing that has been shown to be quite effective at finding bugs in programs. However, to find intricate bugs, often a lot of work has to be spent on test data generators, and a lot of insight is required. A dedicated search procedure could alleviate some of that work. Also, random testing would not work at all for finding solutions to search problems, or inverting a function.



As an example, imagine we have made a large recursive datatype |T| and have just written a |show| function for it:
\begin{code}
show :: T -> String
\end{code}
We would like to find out whether this |show| function is ambiguous, i.e.\ are there different elements in |T| that map to the same string? A property in QuickCheck-style would look something like this:
\begin{code}
prop_Unambiguous :: T -> T -> Property
prop_Unambiguous x y = x /= y ==> show x /= show y
\end{code}
Even if two such elements |x| and |y| exist, it is very unlikely that we would find them using random testing. Instead, one either has to write a dedicated generator for pairs of elements |(x,y)| that are likely to map to the same string (requiring deep insights about the |show| function and where the bug may be), or implement the inverse of the |show| function, a {\em parser}, to be able to say something like this:
\begin{code}
prop_Unambiguous' :: T -> Property
prop_Unambiguous' x = all (x ==) (parse (show x))
\end{code}
Implementing a parser is much harder than a |show| function, which makes this an even less attractive option.

The tool we present in this paper can easily find pairs of such elements on the original property |prop_Unambiguous|, even for quite large sets of mutually recursive datatypes.

There already exist dedicated search procedures for inputs that lead to certain outputs. Most notably, there are a number of tools (such as Reach \cite{reach}, Lazy SmallCheck \cite{lazysc}, and Agsy \cite{agsy}) that employ a backtracking technique called {\em lazy narrowing} to search for inputs. These tools are much better than random testing at finding intricate inputs, but they have one big shortcoming: they employ a depth-limitation on the input. In order to use these tools, a maximum search depth has to be specified (or the tool itself can enumerate larger and larger depths). Increasing the maximum depth of a set of terms affects the size of the search space exponentially. For example, Lazy SmallCheck times out for instances of |prop_Unambiguous| when the depth gets larger than ~4, because there are just too many cases to check.

To overcome this depth problem, we do not limit the search by depth. Rather, we provide a different way of bounding the input, namely by letting the solver carefully expand the input one (symbolic) constructor at a time, carving out an input shape rather than an maximal input depth. We also hope that the sophisticated search strategies in a SAT-solver are able to beat a backtracking search, as long as the encoding of the search problem in SAT is natural enough for the solver to work with.

This paper contains the following contributions:

\begin{itemize}
\item We present a monadic DSL for constraint generation that can be used
to program with a SAT-solver. (Section 3)

\item We show how to express values of arbitrary datatypes symbolically in a SAT-solver. (Section 3)

\item We show programs containing recursive functions over datatypes can be symbolically executed, resulting in a SAT-problem. (Section 4)

\item We show how we can battle certain kinds of exponential blow-up that naturally happen in symbolic evaluation, by means of memoization and a novel program transformation. (Section 4)

\item We show to perform bounded model checking {\em incrementally} for growing input sizes, by making use of feedback from the SAT-solver. (Section 5)
\end{itemize}
We also show a number of different examples, and experimental evaluations on these examples (Section \ref{examples}).

