\section{Symbolic datatypes}
\label{ite}

This section gives a some background and motivation to the techniques we use later in the paper.

The programming language FL, part of the formal verification system Forte \cite{forte} is an ML-like language with one particular distinguishing feature: symbolic booleans. FL has a primitive function with the following type\footnote{Throughout the paper, we use Haskell notation for our examples, even though the examples may not actually be written in the Haskell language.}:
\begin{code}
var :: String -> Bool
\end{code}
The idea behind |var| is that it creates a symbolic boolean value with the given name. It is possible to use the normal boolean operators (|(/\)|, |(\/)|, |(not)|, |(==)|, etc.) on these symbolic booleans, and the result is then computed as a normalized boolean formula in terms of the variables created by |var|. The implementation of FL uses BDDs \cite{bdd} for this.


What happens when we use \ifthenelse{} with these symbolic booleans to choose between, for example, two given lists? This is unfortunately disallowed in FL, and leads to a run-time error. The Haskell library Duck Logic \cite{duck-logic} provided a similar feature to FL, but used the type system to avoid mixing symbolic booleans with regular Haskell values, by making symbolic booleans |BoolSym| a different type from regular |Bool|.

This paper aims to lift this restriction, and allow for all values in the program to be symbolic.
The problem presented by an expression such as:
\begin{code}
if var "a" then [1] else []
\end{code}
is that at symbolic evaluation time, we cannot decide which constructor to return. One of our main ideas in this paper is to transform algebraic datatypes with several constructors, for example:
\begin{code}
data List a = Nil | Cons a (List a)
\end{code}
into a algebraic datatype with only one constructor which is the ``superposition state'' of all possible constructors, that contains enough symbolic boolean variables to decide which constructor we actually have, plus a ``superposition'' of all possible arguments. Here is what we could do for lists:



\begin{code}
data ListSym a = NilCons BoolSym (Maybe (a, ListSym a))

nil :: ListSym a
nil = NilCons FalseSym Nothing

cons :: a -> ListSym a -> ListSym a
cons x xs = NilCons TrueSym (Just (x, xs))
\end{code}
Here, |Maybe| is the regular Haskell datatype, not the symbolic datatype. A symbolic list is thus always built using the |NilCons| constructor. The first argument (a symbolic bool) indicates which constructor we are using (|FalseSym| for |Nil|, |TrueSym| for |Cons|), and the second argument contains the arguments to the |Cons| constructor (which are only used in the case when we actually have a |Cons| constructor).

An extra datatype invariant has to be respected. For |ListSym| it is that whenever it is possible for the constructor to be |True|, the second argument cannot be |Nothing|.

What have we gained from this? It is now possible to implement \ifthenelse{} on lists, in terms of \ifthenelse{} on symbolic booleans and list elements. Here is the implementation:




\begin{code}
if b then NilCons c1 ma1 else NilCons c2 ma2 =
  NilCons  (if b then c1   else c2)
           (if b then ma1  else ma2)
\end{code}
We also need \ifthenelse{} on the regular |Maybe| type, which in a symbolic setting is only used to indicate the presence or absence of constructor arguments:


\begin{code}
if b then Nothing  else ma2      = ma2
if b then ma1      else Nothing  = ma1
if b then Just a1  else Just a2  =
  Just (if b then a1 else a2)
\end{code}
If one branch does not have arguments, we choose the other side. If both branches have arguments, we choose between them.

How can we do |case|-expressions on these symbolic lists? It turns out having \ifthenelse{} on the result type is enough. If we have a |case|-expression:
\begin{code}
case xs of
  Nil        -> a
  Cons y ys  -> f (y,ys)
\end{code}
we can translate it to work on symbolic lists as follows:
\begin{code}
let NilCons c ma = xs in
  if c then f (fromJust ma) else a
\end{code}
In this way, the user can use boolean variables to create a symbolic input to a program, for example representing all lists up to a particular length, containing elements up to a particular size, and run the program. The output will be another symbolic expression, about which we can ask questions. For example, if we want to do property checking, the output will be a symbolic boolean, and we can ask if it can ever be |FalseSym|.

In the remainder of the paper we will use the main idea described in this section, with a number of changes. Firstly, we are going to use a SAT-solver instead of BDDs. Also, we want to create inputs to the program {\em incrementally}, without deciding up-front how large the inputs should be.
For these reasons, we move from an {\em expression-based} view (using \ifthenelse{}) to a {\em constraint-based} view.

% ------------------------------------------------------------------------------

\section{A DSL for generating constraints}
\label{dsl}

In this section, we present a small DSL, the constraint monad, that we will use later for generating constraints to a SAT-solver. We also show, by means of examples, how it can be used to encode algebraic datatypes symbolically.

\subsection{The Constraint monad}

We start by explaining the API of the monad we use to generate constraints. We make use of an abstract type |Prop|, that represents propositional logic formulas. (The type |Prop| plays the same role as the type |BoolSym| above.)





\begin{code}
type Prop

(/\), (\/), (==>), (<=>)  :: Prop -> Prop -> Prop
(nt)                      :: Prop -> Prop
true, false               :: Prop
\end{code}
Note however that there is no way to create a variable with a given name of type |Prop|. Variable creation happens inside the constraints generating monad |C|, using the function |newVar|:
\begin{code}
type C a
instance Monad C

newVar  :: C Prop
insist  :: Prop -> C ()
when    :: Prop -> C () -> C ()
\end{code}
We can use the function |insist| to state that a given proposition has to hold. In this way, we generate constraints.

The function |when| provides a way of keeping track of local assumptions. The expression |when a m| generates all constraints that are generated by |m|, but they will only hold conditionally under |a|. To explain better what |when| does, consider the following equivalences:

\begin{code}
when a (insist b)  ===  insist (a ==> b)
when a (when b m)  ===  when (a /\ b) m
when false m       ===  return ()
\end{code}
These are logical equivalences, i.e.\ the expressions on the left and right hand side may generate syntactically different sets of constraints, but they are logically equivalent.

|C| can be thought of as a reader monad in the environment condition (hereafter called the {\em context}), a writer monad in the constraints, and a state monad in variable identifiers. In reality, it is implemented on top of a SAT-solver (in our case, we are using MiniSat \cite{minisat}). The function |newVar| simply creates a new variable in the solver, |insist| generates clauses from a given proposition and the environment condition, and |when| conjoins its proposition argument with the current environment condition to generate the environment for its second argument.

\subsection{Finite choice}

In order to help us define the translation from algebraic datatypes to monadic constraint generating code, we introduce the following abstraction. The type |Fin a| represents a symbolic choice between finitely many concrete values of type |a|.
\begin{code}
newtype Fin a = Fin [(Prop,a)]

newFin :: Eq a => [a] -> C (Fin a)
newFin xs = do  ps <- sequence [ newVal | x <- nub xs ]
                insist (exactlyOne ps)
                return (Fin (ps `zip` nub xs))

one :: a -> Fin a
one x = Fin [(true,x)]

is :: Eq a => Fin a -> a -> Prop
Fin pxs `is` x = head ([p | (p,y) <- pxs, x == y] ++ [false])
\end{code}
The function |newFin| creates a suitable number of new variables, uses a proposition function |exactlyOne| that creates a formula expressing that exactly one of its arguments is true, and returns |Fin a| value which relates the values from |xs| to the corresponding propositional variables. The function |one| creates a |Fin a| with only one option. The function |is| selects the proposition belonging to the given value.

\subsection{Incrementality}

Before we show the symbolic encoding of datatypes in the constraint generation setting, we need to introduce one more auxiliary type. Since we are going to create symbolic inputs to programs {\em incrementally}, i.e.\ without knowing on beforehand how large they should be, we introduce the type |Delay|\footnote{As we shall see in Section \ref{sec:solving}, the story is slightly more complicated than this, but we present a simplified version here for presentation purposes.}.
\begin{code}
type Delay a

delay  :: C a -> C (Delay a)
done   :: a -> Delay a
force  :: Delay a -> C a
wait   :: Delay a -> (a -> C ()) -> C ()
\end{code}
Using the function |delay|, we can created a delayed computation of type |Delay a|, which will be executed at most once. For convenience, the function |done| also creates a delayed computation, but one which is already done.
Using |force|, we can make a delayed computation happen. Using |wait|, we can make code wait for a delayed computation to happen, and react to it by executing its second argument.

The way |Delay| is implemented is the standard way lazy thunks are implemented in an imperative setting, using |IORef|s, as follows:
\begin{code}
data Delay a  =  Done a
              |  Delay (IORef (Either (C ()) a))
\end{code}
A |Delay| is either an already evaluated value, or a mutable reference filled with either a constraint generator that, when run, will fill the reference with a value, or a value.

In order to use references in the |C|-monad, we lift the standard |IORef| functions into the |C|-monad:
\begin{code}
newRef    :: a -> C (IORef a)
readRef   :: IORef a -> C a
writeRef  :: IORef a -> a -> C ()
\end{code}
In Section \ref{sec:input}, a more detailed implementation of |Delay|s is given. In the next subsection, we will see how |Delay| is used.

\subsection{Symbolic datatypes}

In the previous section, we saw how we could make an algebraic datatype symbolic by creating one constructor that is the ``superposition'' of all constructors, with arguments (1) a symbolic value indicating which constructor we have, and (2) the union of all possible arguments to the constructors.

In this subsection, we show how to do this in our constraint-based setting, by example, and using a different datatype, namely of arithmetic expressions:
\begin{code}
data Expr a  =  Var a
             |  Add (Expr a) (Expr a)
             |  Mul (Expr a) (Expr a)
             |  Neg (Expr a)
\end{code}
The first thing we need to do to create a symbolic version of this datatype
is to make a new datatype representing the choice of constructors:
\begin{code}
data ExprL = Var | Add | Mul | Neg deriving ( Eq )
\end{code}
The second thing we do is to merge all constructor arguments into one symbolic constructor:

\begin{code}
data Arg a    = X | An a

data ExprC s  = Expr (Fin ExprL)  (Arg a)
                                  (Arg (ExprSym a))
                                  (Arg (ExprSym a))
\end{code}
The new constructor |Expr| has one argument of type |Fin ExprL| that indicates (symbolically) which constructor we are using. The other arguments are the (multi-set) union of all arguments that are used by any of the original constructors. We use the type |Arg|, which is isomorphic to the Haskell |Maybe| type to indicate that some arguments may not always be present.
In the merged constructor |Expr|, we reuse argument positions as much as possible; for example the first arguments of |Add|, |Mul|, and |Minus| are all represented by one argument of the symbolic |Expr| constructor.

We are enforcing a datatype invariant that guarantees that an |Arg| argument is not |X| when it is possible that the constructor has the corresponding argument.

Finally, we define the actual type of symbolic expressions, by using the |Delay| type:
\begin{code}
type ExprSym a = Delay (ExprC a)
\end{code}
A symbolic expression is thus an object that can potentially create a choice of constructors, plus the choice of arguments, which in turn can be symbolic expressions again.

All recursive types have to use the |Delay| constructor, because in general we cannot know in advance what the size is. With |Delay|, we can delay this decision until later, when we see what happens when we evaluate the program.

For convenience, we create the following helper functions that represent the old constructor functions:
\begin{code}
var       :: a -> ExprSym a
add, mul  :: ExprSym a -> ExprSym a -> ExprSym a
neg       :: ExprSym a -> ExprSym a

var x    = done (Expr (one Var) (An a)  X       X)
add a b  = done (Expr (one Add) X       (An a)  (An b))
mul a b  = done (Expr (one Add) X       (An a)  (An b))
neg a    = done (Expr (one Neg) X       (An a)  X)
\end{code}

In general, to make a symbolic version of an algebraic datatype |Type|, we create three new types: |TypeL|, which enumerates all constructor functions from |Type|; |TypeC|, which has one argument of type |Fin TypeL| and moreover the union of all constructor arguments tagged with |Arg|, and |TypeSym|, which is just |Delay TypeC|. Note that this construction also works for mutally recursive datatypes.

We have seen how to construct concrete values in these symbolic datatypes. What is left is to show how to do case analysis on symbolic datatypes, how to construct symbolic values, and how to state equality between . This is presented in the next two subsections.

\subsection{Case expressions on symbolic datatypes}

In a regular case analysis, three things happen: (1) the scrutinee is evaluated, (2) the constructor is examined to make a choice between branches, and (3) the arguments of the constructor are bound in the correct branch.

On symbolic datatypes, we split case analysis in three parts as well. However, our case analysis is {\em passive}; it does not demand any evaluation, instead it will wait until another part of the program defines the scrutinee, and then generate constraints.

To examine which constructor we have, we introduce the following helper functions:
\begin{code}
isVar, isAdd, isMul, isNeg :: ExprC a -> Prop
isVar  (Expr c _ _ _)  = c `is` Var
isAdd  (Expr c _ _ _)  = c `is` Add
isMul  (Expr c _ _ _)  = c `is` Mul
isNeg  (Expr c _ _ _)  = c `is` Neg
\end{code}
And to project out relevant arguments, we use the following projection functions:



\begin{code}
sel1 :: ExprC a -> a
sel2 :: ExprC a -> ExprSym a
sel3 :: ExprC a -> ExprSym a

sel1 (Expr _ (An x) _ _)  = x
sel2 (Expr _ _ (An a) _)  = a
sel3 (Expr _ _ _ (An b))  = b
\end{code}
Note that the $\mathit{sel}_i$ functions are partial; we should not use them when the corresponding arguments do not exist.
Now, to express a case expression of the following form on a symbolic datatype:





\begin{code}
case e of
  Var x    -> P1//-[x]
  Add a b  -> P2//-[a,b]
  Mul a b  -> P3//-[a,b]
  Neg a    -> P4//-[a]
\end{code}
We write the following:
\begin{code}
wait e § \ec ->
  do  when (isVar ec)  §  P1//-[sel1 ec]
      when (isAdd ec)  §  P2//-[sel2 ec,sel3 ec]
      when (isMul ec)  §  P3//-[sel2 ec,sel3 ec]
      when (isNeg ec)  §  P4//-[sel2 ec]
\end{code}
First, we wait for the scrutinee to be defined, then we generate 4 sets of constraints, one for each constructor.

\subsection{Creating symbolic values}

We have seen how we can create concrete symbolic values (using |var|, |add|, |mul|, and |neg|), but not how to create values with symbolic variables in them.

Creating these kinds of values turns out to be so useful that we introduce a type class for them:
\begin{code}
class Symbolic a where
  new :: C a
\end{code}
Here are some instances of types we have seen before:
\begin{code}
instance Symbolic Prop where
  new = newVal

instance Symbolic a => Symbolic (Arg a) where
  new = An `fmap` new

instance Symbolic a => Symbolic (Delay a) where
  new = delay new
\end{code}
We already know how to generate symbolic |Prop|s. When generating a completely general symbolic |Arg|, it has to exist (it cannot be |X|). Generating a symbolic |Delay| just delays the generation of its contents, which is how we get incrementality. Generating a symbolic tuple means generating symbolic elements.

When we make a new symbolic datatype |TypeSym|, we have to make an instance of |Symbolic| for its constructor type |TypeC|. Here is what it looks like for |ExprC|:
\begin{code}
instance Symbolic a => Symbolic (ExprC a) where
  new =  do  c <- newFin [Var,Add,Mul,Neg]
             liftM3 (Expr c) new new new
\end{code}
With the instance above, we also have |new :: C ExprSym| to our disposal.

\subsection{Copying symbolic values} \label{sec:copy}

The last operation on symbolic types we need is {\em copying}. Copying is needed when we want to generate constraints that define a symbolic value |y| in terms of a given value |x|. Copying is also used a lot, and therefore we introduce a type class:

\begin{code}
class Copy a where
  (>>>) :: a -> a -> C ()
\end{code}
The expression |x >>> y| copies |x| into |y|; it defines |y| as |x| under the current environment condition.

Here are some instances of types we have seen before:
\begin{code}
instance Copy Prop where
  p >>> q = insist (p <=> q)

instance Eq a => Copy (Fin a) where
  Fin pxs >>> v = sequence_
    [ insist (p ==> (v `is` x)) | (p,x) <- pxs ]

instance Copy a => Copy (Delay a) where
  s >>> t = wait s § \x -> do  y <- force t
                               x >>> y
\end{code}
For |Prop|, copying is just logical equivalence. For finite values |Fin a|, we let the propositions in the left argument imply the corresponding propositions in the right argument. This is enough because all propositions in a |Fin a| are mutually exclusive.

For |Delay a|, we wait until |s| gets defined, and as soon as this happens, we make sure |t| is defined (if it wasn't already), and copy the contents of |s| to the contents of |t|.

At this stage, it may be interesting to look at an example of a combination of |new| and |>>>|. Consider the following two |C|-expressions:



\begin{code}
do  y <- new  ///  ===  /// do x >>> z
    x >>> y
    y >>> z
\end{code}
Both logically mean the same thing, if |y| is not used anywhere else. The left hand side creates a new |y|, copies |x| into |y| and also copies |y| into |z|. The first copy constraint has the effect of always making sure that |y| is logically equivalent to |x| under the current environment condition. As soon as any |Delay| in |x| becomes defined, which may happen after these constraints have been generated, |y| will follow suit. And whenever |y| expands a |Delay|, |z| will follow suit. So the effect of the left hand side is the same as the right hand side.

To enable copying on symbolic datatypes |TypeSym| we need to make an instance for their corresponding |TypeC|. Here is what this looks like for |ExprC|:




\begin{code}
instance Copy a => Copy (ExprC a) where
  Expr c1 x1 a1 b1 >>> Expr c2 x2 a2 b2 =
    do  c1 >>> c2
        when (isVar c1)  §  do x1 >>> x2
        when (isAdd c1)  §  do a1 >>> a2; b1 >>> b2
        when (isMul c1)  §  do a1 >>> a2; b1 >>> b2
        when (isNeg c1)  §  do a1 >>> a2
\end{code}
We can see that copying runs the same recursive call to |>>>| multiple times in different branches. However, we should not be calling these branches, because in one general symbolic call to the above function, {\em all} ``branches'' will be executed! This means that the same recursive call will be executed several times, leading to an exponential blow-up. In Section \ref{sec:memo} we will see how to deal with this.

% ------------------------------------------------------------------------------

\section{Translating programs into constraints}




In this section, we explain how we can translate a program |p :: A -> B| in a simple functional programming language into a monadic program |pSym :: ASym -> C BSym| in Haskell, such that when |pSym| is run on symbolic input, it generates constraints in a SAT-solver that correspond to the behavior of |p|.

For now, we assume that the datatypes and programs we deal with are first-order. We also assume that all definitions are total, i.e.\ terminating and non-crashing. We will later have a discussion on how these restrictions can be lifted.

\subsection{The language}

We start by presenting the syntax of the language we translate. This language is very restricted syntactically, but it is easy to see that more expressive languages can be translated into this language.

Function definitions |d| and recursion can only happen on top-level. A program is a sequence of definitions |d|.








\begin{code}
d ::= f x1 ... xn = e
\end{code}
Expressions are separated into two categories: {\em simple} expressions and regular expressions. Simple expressions are constructor applications, selector functions, or variables. Regular expressions are let-expressions with a function application, case-expressions, or simple expressions.
\begin{code}
s ::=  K s1 ... sn
    |  sel s
    |  x

e ::=  let x = f s1 ... sn in e
    |  case s of
         K1 -> e1
         ...
         Kn -> en
    |  s
\end{code}
Function application can only happen inside a let-definition and only with simple expressions as arguments. Case-expressions can only match on constructors, the program has to use explicit selector functions to project out the arguments.

As an example, consider the definition of the standard Haskell function |(++)|:
\begin{code}
(++) :: [a] -> [a] -> [a]
[]      ++ ys  = ys
(x:xs)  ++ ys  = x : (xs ++ ys)
\end{code}
In our restricted language, this function definition looks like:
\begin{code}
xs ++ ys = case xs of
             Nil   ->  ys
             Cons  ->  let vs = sel2 xs ++ ys
                       in Cons (sel1 xs) vs
\end{code}

\subsection{Basic translation}



The translation revolves around the basic translation for expressions, denoted |transr e r|, where |e| is a (simple or regular) expression, and |r| is a variable. We write |transr e r| for the monadic computation that generate constraints that copy the symbolic value of the expression |e| into the symbolic value |r|.

Given the translation for expressions, the translation for function definitions is:
\begin{code}
trans (f x1 ... xn = e) /// = /// f x1 ... xn = do  y <- new
                                                    transr e y
                                                    return y
\end{code}
To translate a function definition, we generate code that creates a new symbolic value |y|, translates |e| into |y|, and returns |y|.

The translation for simple expressions is simple, because no monadic code needs to be generated; we have pure functions for concrete data constructors and pure functions for selectors.
\begin{code}
transr s r /// = /// s >>> r
\end{code}
We simply copy the value of the simple expression into |r|.

To translate let-expressions, we use the standard monadic transformation:
\begin{code}
transr (let f s1 ... sn in e//) r /// = /// do  x <- f s1 ... sn
                                                transr e r
\end{code}
To translate case-expressions, we use |wait| to wait for the result to become defined, and then generate code for all branches.


\begin{code}
transr (case s of         ///  =  ///  wait s § \cs ->
          K1 -> e1        ///  ¤  ///  ///   do  when (isK1 cs)  §  transr e1 r
          ...             ///  ¤  ///            ...
          Kn -> en //) r  ///  ¤  ///            when (isKn cs)  §  transr en r
\end{code}

\subsection{A translated example}

Applying our translation to this function and using symbolic lists, yields the following code:


\begin{code}
(++?) :: Symbolic a => ListSym a -> ListSym a -> C (ListSym a)
xs ++? ys = do  zs <- new
                wait xs § \cxs ->
                  when (isNil cxs) §
                    do  ys >>> zs
                  when (isCons cxs) §
                    do  vs <- sel2 cxs ++ ys
                        cons (sel1 cxs) vs >>> zs
\end{code}
An example property that we may use to find a counter example to may look like this:
\begin{code}
appendCommutative xs ys =
  do  vs <-  xs ++? ys
      ws <-  ys ++? xs
      b  <-  vs ==? ws
      insist (nt b)
\end{code}
We use the symbolic version |(==?)| of |(==)| that is generated by our translation. When we run the above computation, constraints will be generated that are going to search for inputs |xs| and |ys| such that |xs++ys == ys++xs| is false.

\subsection{Memoization} \label{sec:memo}

When performing symbolic evaluation, it is very common that functions get applied to the same arguments more than once. This is much more so compared to running a program on concrete values. A reason for this is that in symbolic evaluation, {\em all} branches of every case expression are potentially executed. If two or more branches contain a function application with the same arguments (something that is even more likely to happen when using selector functions), a concrete run will only execute one of them, but a symbolic run will execute all of them. A concrete example of this happens in datatype instances of the function |(>>>)| (see Section \ref{sec:copy}).

An easy solution to this problem is to use memoization. We apply memoization in two ways.

First, for translated top-level function calls that return a result, we keep a memo table that remembers to which symbolic arguments a function has been applied. If the given arguments has not been seen yet, a fresh symbolic result value |r| is created using |new|, and the function body |e| is run {\em in a fresh context} |c|. The reason we run |e| in a fresh context is that we may reuse the result |r| from many different future contexts. In order to use the result |r| from any context, we need to make the context |c| true first (by using |insist|). After storing |c| and |r| in |f|'s memo table, we return |r|. If we have already seen the arguments, we simply return the previously computed result, after making sure to imply the context in which it was created.

Translating a definition |f x1 ... xn = e| with memoization on thus yields the following result:
\begin{code}
f x1 ... xn =
  do  mcy <- lookMemo_f x1 ... xn
      case mcy of
          Nothing     -> do  c <- new
                             y <- new
                             storeMemo_f x1 ... xn (c,y)
                             with c § transr e y
                             insist c
                             return y

          Just (c,y)  -> do  insist c
                             return y
\end{code}
The functions |lookMemo_f| and |storeMemo_f| perform lookup and storage in |f|'s memo table, respectively. The function |with| locally sets the context for its second argument.

Second, we also memoize the copy function |(>>>)|. This function is not a function that returns a result, but it generates constraints instead. However, we treat |(>>>)| as if it were a top-level function returning |()|, and memoize it in the same way.

Memoization can have big consequences for the performance of constraint generation and solving, as shown in the experimental evaluation.
We allow memoization to be turned on and off manually for each top-level function. We always memoize |(>>>)| on |Delay|.

\subsection{Symbolic merging of function calls}

Consider the following program:
\begin{code}
f e =  case e of
         Var v    -> v
         Add a b  -> f a
         Mul a b  -> f b
         Neg a    -> f a
\end{code}
In the previous subsection, we explained that all branches of a case expression have to be explored when performing symbolic evaluation. This is obviously bad when there exist identical function calls that occur in multiple branches. But it is also bad when there are multiple branches that contain a call to the same function |f|, even when those calls do not have the same arguments. A run of |f| on concrete values would take linear time in the depth $k$ of the argument expression. A naive symbolic run of |f| would take time proportional to $3^k$! After applying memoization, this is reduced to $2^k$. However, we would like to get as closely to linear in $k$ as possible.

Consider the following transformed version of the above program, after applying standard program transformations.

\begin{code}
f e =  let y = f (  case e of
                      Var v    -> undefined
                      Add a b  -> a
                      Mul a b  -> b
                      Neg a    -> a )
       in  case e of
             Var v    -> v
             Add a b  -> y
             Mul a b  -> y
             Neg a    -> y
\end{code}
This program behaves the same as the original program (at least in a lazy semantics), but now it only makes one recursive call, {\em even when we symbolically evaluate it}. The trick is to share one generalized call to |f| between all 3 places that need to call |f|. We can do this, because those 3 places never really need to call |f| at the same time; for any concrete input, we can only be in one branch at a time. Thus, we have {\em merged} three calls to |f| into one call.

Our translator can generate constraint producing code that applies the same idea as the above program transformation, but directly expressed in constraint generation code. In order for this to happen, the user has to manually annotate calls to |f| with a special labelling construct |@|:
\begin{code}
f e =  case e of
         Var v    -> v
         Add a b  -> (f a)@ 1
         Mul a b  -> (f b)@ 1
         Neg a    -> (f a)@ 1
\end{code}
The generated constraint producing code will look like this:

\begin{code}
fSym e = do  r <- new
             wait e § \ce ->
               do  c <- new
                   x <- new
                   y <- with c § fSym x

                   when (isVar ce) §  do  sel1 ce >>> r
                   when (isAdd ce) §  do  insist c
                                          sel2 ce >>> x
                                          y >>> r
                   when (isMul ce) §  do  insist c
                                          sel3 ce >>> x
                                          y >>> r
                   when (isNeg ce) §  do  insist c
                                          sel2 ce >>> x
                                          y >>> r
\end{code}
The above function first waits for its argument to be defined, and then creates a fresh context |c| and a fresh input |x|, and then it evaluates |fSym| with the input |x| in the context |c|. Then, the normal part of the case expression progresses, but instead of calling |fSym|, the branches simply use |insist| to make sure the context of the merged call is set, and copy the argument they need into |x|. This guarantees that |y| gets the correct value. An interesting thing to notice is that, because we are generating constraints and not evaluating values,

Note that in the above code, because |(>>>)| is memoized, the call |y >>> r| only gets performed once although it appears in the code three times, and |sel2 ce >>> x| also gets performed only once although it appears twice.

Our experimental evaluation also shows the importance of merging function calls in case branches. Automatically knowing when and where to apply the labels of function calls that should be merged is future work.

\subsection{Other optimizations}

We perform a few other optimizations in our translation. Two of them are described here.

Not all algebraic datatypes need to use |Delay|. In principle, for any finite type we do not need to use |Delay| because we know the (maximum) size of the elements on beforehand. In our translator, we decided to not use |Delay| for enumeration types (e.g.\ |BoolSym|).

For definitions that consist of a simple expression |s|, we can translate as follows:
\begin{code}
trans (f x1 ... xn = s) /// = /// f x1 ... xn = do  return s
\end{code}
This avoids the creation of an unnecessary helper value using |new|.

% ------------------------------------------------------------------------------

\section{Solving the constraints} \label{sec:solving}

In the previous two sections, we have seen how to generate constraints in the |C| monad, and how to translate functional programs into constraint producing programs. However, we have not talked about how to actually generate symbolic inputs to programs, and how to use the SAT-solver to find solutions to these constraints. In order to do this, we have to make part of the code we have shown so far slightly more complicated.

\subsection{Inputs and internal points} \label{sec:input}

In a symbolic program, there are two kinds of symbolic expressions: inputs and internal points. They are dealt with in two fundamentally different ways. Inputs are expressions that are created outside of the program, and that are controlled by the solver. If the solver determines that a certain input should be made bigger by expanding one of its delays, it can do so, and the program will react to this, by triggering constraint generators that are waiting for these delays to appear. These triggers may in turn define other delays (by using |>>>|), and a cascade of constraint generators will be set in motion. So, inputs are set on the outside, and internal points react to their stimuli.

We would like to make this difference explicit by introducing two functions to create symbolic expressions: one called |new| for internal points, and one called |newInput| for inputs. To implement this, we introduce a new datatype of |Mode|s, with which symbolic expressions can be labelled.
\begin{code}
data Mode = Input | Internal
\end{code}
The most important place where the label should occur is when we create a |Delay|. We make the following changes:

\begin{code}
data Delay a  =  Done a
              |  Delay Mode (IORef (Either (C ()) a))

delay :: Mode -> C a -> C (Delay a)
delay m c =
  mdo  ref <-  newRef § Left §
                 do  a <- c
                     writeRef ref (Right a)
       return (Delay m ref)
\end{code}
The function |delay| gets an extra |Mode| argument, which indicates what kind of delay we are creating.

Whenever we create any new symbolic value, we need to be explicit about what kind of value we are creating. We therefore change the |Symbolic| class accordingly:
\begin{code}
class Symbolic a where
  newMode :: Mode -> C a

new, newInput :: Symbolic a => C a
new       = newMode Internal
newInput  = newMode Input
\end{code}
The function |new| now always creates internal points, where as the new function |newInput| creates new inputs.

The mode information needs to be propagated through all calls of |newMode|:
\begin{code}
instance Symbolic Prop where
  newMode _ = newVal

instance Symbolic a => Symbolic (Arg a) where
  newMode m = An `fmap` newMode m

instance Symbolic a => Symbolic (Delay a) where
  newMode m = delay m (newMode m)

instance Symbolic a => Symbolic (ExprC a) where
  newMode m =  do  c <- newFin [Var,Add,Mul,Neg]
                   liftM3  (Expr c) (newMode m)
                           (newMode m) (newMode m)
\end{code}
What is now the different between delays that belong to inputs and delays that belong to internal points? Well, if the program decides to do a |wait| on an internal point, then the algorithm that controls the expansion of the input delays does not need to know this. Internal points are only expanded by the program. But if the program decides to do a |wait| on an input delay, the algorithm that controls the expansion needs to know about it, because now this delay is a candidate for expansion later on.

To implement this, we introduce one more function to the |C| monad:
\begin{code}
enqueue :: Delay a -> C ()
\end{code}
We augment |C| to also be a state monad in a queue of pairs of contexts and delays. The function |enqueue| takes a delay and adds it to this queue together with the current context.

The function |enqueue| is called by the function |wait| when it blocks on an input delay:
\begin{code}
wait :: Delay a -> (a -> C ()) -> C ()
wait (Done x)         k = k x
wait d@(Delay m ref)  k =
  do  ecx <- readRef ref
      case ecx of
        Left cx  -> do  c <- ask
                        writeRef ref § Left §
                          do  cx
                              Right x <- readRef ref
                              with c § k x
                        case m of
                          Input     -> enqueue d
                          Internal  -> return ()

        Right x  -> do  k x
\end{code}
When a |C| computation terminates and has generated constraints, we can look at the internal queue and see exactly which parts of the inputs (input delays) are requested by which parts of the program (contexts), and in which order this happened.

\subsection{Solving and expanding}

The main loop we use in our solving algorithm works as follows. We start by creating a SAT-solver, and
running the main |C|-computation. This will produce a number of constraints in the SAT-solver. It will also produce a queue $Q$ of pairs of contexts and unexpanded input delays.

We then enter our main loop.

The first step in the loop is to find out whether or not there exists an actual solution to the current constraints. The insight we employ here is that a real solution (i.e.\ one that corresponds to an actual run of the program) cannot enter any of the contexts that are currently in the queue. This is because those contexts all have pending input delays: case expressions that have not been triggered yet. In other words, the constraints belonging to those contexts are not finished yet; there may yet be more to come. So, when looking for a real solution, we ask the SAT-solver to find a solution to all constraints generated so far, under the assumption that all of the contexts that appear in the queue $Q$ are false. If we find a solution, we can from the model produced by the SAT-solver read off the actual values of the input that satisfy the constraints.

If we do not find a solution, it may be because we still had to expand one of the contexts in the queue $Q$. So, we have to pick an element from the queue, for which we are going to expand the corresponding |Delay|. The simplest choice we can make here is just to pick the first element from the queue, expand the delay contained in it, remove all occurrences of that delay in the queue $Q$, and repeat the main loop. If we do this, we get a completely fair expansion, which leads to an algorithm that is both sound and complete. Soundness here means that any found solution actually corresponds to a real run of the program, and completeness means that we are guaranteed to find a solution if there exists one.

But we can do better. The SAT-solver is able to give feedback about our question of finding a solution under the assumption that all contexts in the queue $Q$ are false. When the answer is no, we also get a {\em subset} of the assumptions for which the SAT-solver has discovered that there is no solution (this subset is called the {\em assumption conflict set} \cite{minisat}, or sometimes an {\em unsatisfiable core}). Typically, the assumption conflict set is much smaller than the original assumption set. An improved expansion strategy picks a context to expand from the assumption conflict set. It turns out that if always we pick the context from the conflict set that is closest to the front of the queue $Q$, then we also get a sound and complete expansion strategy.

Why is this better? There may be lots of contexts that are waiting for an input to be expanded, but the SAT-solver has already seen that there is no reason to expand those contexts, because making those contexts true would violate a precondition for example. The assumption conflict set is a direct way for the solver to tell us: ``If you want to find a solution, you should make one of these propositions true''. We then pick the proposition from that set that leads to the most fair expansion strategy.

To see why this strategy is complete, consider the case where the full constraint set has a solution $s$, but we are not finding it because we are expanding the wrong delays. In that case, there must after a while exist a finite, non-empty set $S$ of delays in $Q$ that should be expanded in order to reach the desired solution, but that are never chosen when we do choose to expand a delay. (If this does not happen, we will find the solution eventually.) The first observation we make is that for every conflict set that is found, at least one element from $S$ must be a part of it. (If not, this would imply that $s$ was not a solution after all.) Since the expansion strategy does not pick points from $S$ to expand, it picks points that lie closer to the front of the queue instead. But it cannot pick such points infinitely often; eventually the points in $S$ must be the ones closest to the head.

In our experimental evaluation we show that this expansion strategy very often defines just the right constructors in the input in order to find the counter example, even for large examples. We thus avoid having to pick a depth-limit up-front, and even avoid reasoning about depth altogether.

An additional bonus of using the assumption conflict set is that when that set is empty, it is guaranteed that no solution can be found, ever, and the search can terminate. This typically happens if the user constrained the input using size and/or depth constraints, but it can happen in other cases as well.

\subsection{Dealing with non-termination}
\label{postpone}

So far, we have assumed that all functions terminate. However, it turns out that this restriction is unnecessary; there is a simple trick we can employ to deal with functions that may not terminate: For possibly non-terminating functions, we use a special function |postpone|:
\begin{code}
postpone :: C () -> C ()
postpone m =  do  x <- newInput
                  wait x § \ () -> m
\end{code}
This function takes a constraint generator as an argument, and postpones it for later execution, by simply constructing a new {\em input} to the program, and blocking in that input. The result is that the expansion of the input in the current context now lies in the expansion $Q$, and it is guaranteed that it will be picked some time in the future, if the solver deems the current context part of a promising path to a solution.

For possibly non-terminating functions |f|, |postpone| is used in the following way:
\begin{code}
trans (f x1 ... xn = e) /// = /// f x1 ... xn = do  y <- new
                                                    postpone § transr e y
                                                    return y
\end{code}
The generation of constraints for the body |e| of |f| is postponed until a later time.

It is good that we have postpone; sometimes, even though our input program clearly terminates, the transformed symbolic program may not terminate. This can happen when the static sizes of symbolic arguments to recursive functions do not shrink, whereas they would shrink in any concrete case. An example is the function |merge| after merging recursive function calls, as explained in the experimental evaluation section. The function |postpone| also works in those cases.

Thus, we use |postpone| on any function which is not structurally recursive {\em after} transformation into a symbolic program.

