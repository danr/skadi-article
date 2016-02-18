
\begin{abstract}
We present a new symbolic evaluation method for functional programs that generates input to a SAT-solver. The result is a Bounded Model Checking (BMC) method for functional programs that can find concrete inputs that cause the program to produce certain outputs, or show the inexistence of such inputs under certain bounds. SAT-solvers have long been used for BMC on hardware and low-level software. This paper presents the first method for SAT-based BMC for high-level programs containing algebraic datatypes and unlimited recursion. Our method works {\em incrementally}, i.e. it increases bounds on inputs until it finds a solution. We also present a novel optimization, namely {\em function call merging}, that can greatly reduce the complexity of symbolic evaluation for recursive functions over datatypes with multiple recursive constructors.
\end{abstract}

\keywords
bounded model checking, SAT, symbolic evaluation

