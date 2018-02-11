\documentclass[12pt,a4paper]{scrreprt}

\usepackage[english]{babel}

% Links inside the bibliography
\usepackage[colorlinks=true,linkcolor=teal]{hyperref}

% Type checking for Agda
\usepackage[conor,references]{agda}
% We ought to be able to just change the font used for \mathsf?
\setsansfont{XITS}

% Less margins
\usepackage{fullpage}

% List customization
\usepackage[inline]{enumitem}

\usepackage{todonotes}


\begin{document}

\AgdaHide{
\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
\end{code}}

\begin{titlepage}
    \centering{}

    {\scshape\LARGE University of Strathclyde \par}
    \vspace{1cm}

    {\scshape\Large Submitted for the Degree of B.Sc. in Computer Science \par}
    \vspace{1.5cm}

    {\huge\bfseries Evidence providing problem solvers in Agda \par}
    \vspace{2cm}

    {\Large\itshape Uma Zalakain\par}
    \vfill

    supervised by\par
    Dr. Conor \textsc{McBride}

    \vfill

    {\small
    Except where explicitly stated all the work in this report, including
    appendices, is my own and was carried out during my final year. It has not
    been submitted for assessment in any other context.
    }

    \vfill

    {\large \today \par}
\end{titlepage}


\newpage

%   Introductory Pages Before the chapters of your report, there should be a
%   number of introductory pages. These should include:
%   - the title page (which has a compulsory format),
%   - a page giving an abstract of your work,
%   - an acknowledgements page, and
%   - a table of contents.

\begin{abstract}
\todo{Abstract}
% Proving certain theorems can be boring and we want to automate it
% We don't want just the answer, we want a proof that it is the correct answer
\end{abstract}

\section*{Acknowledgements}

\todo{Acknowledgements}

% I'm very to have a supervisor with a keen interest in these subjects.
% I'm very lucky I had that 3 month intro to Agda.

\tableofcontents

\chapter{Introduction}

%   Introduction This should briefly describe the problem which you
%   set out to solve and should essentially summarise the rest of your
%   report. The aim of an introduction is to convince the reader that
%   they should read on, so it is very important that excessive detail
%   is avoided at this stage.

%   The introduction should include the list of objectives that you
%   identified for the project, as well as a brief overview of the
%   outcome. In its final part, the introduction will usually outline
%   the structure of the rest of the report.

Formal proofs construct theorems by sequentially applying the axioms
of a formal system. Computers can assist this process and make theorem
proving a conversation between the human and the computer that checks
the correctness of the proof. Yet, theorem proving can often be boring
and tedious: certain theorems are trivial or uninteresting but require
many rewrites.

It is in these cases where automated theorem proving shines strongest:
instead of applying inference rules manually, the user can provide the
solver with a proposition and get a verified solution back. These
decision procedures are often based on some meta-theory about the
system, and thus can result in less rewriting steps than the repeated
application of inference rules from inside the system.

This project embarks upon constructing such solvers and proving them
correct. Three different problems will be considered: the first two
will involve solving equalities on algebraic structures, the third one
deciding a first-order predicate logic — Presburger arithmetic. The
aim is to better understand theorem proving as seen through the
Curry-Howard lens.

\todo{Sections}

\chapter{Background}

\section{Proofs as programs; propositions as types}

If a computer is to verify the proof of some proposition, there must
exist some computational model for both proofs and propositions. Such
one was first discovered by Haskell Curry and later strengthened by
William Alvin Howard. It establishes a two way correspondence between
type theory and intuitionistic logic: propositions are isomorphic to
types and proofs are to programs; to prove a proposition is to
construct a program inhabiting its corresponding type. Formal proofs
can be verified by type-checkers.

\todo{Agda 2.5.4 for correct indentation}

\begin{code}
-- Falsehood: an uninhabited type with no constructors
data ⊥ : Set where

-- Ex falso quodlibet
-- Agda can see there is no way of constructing ⊥
explosion : {A : Set} → ⊥ → A
explosion () -- No need to provide a case

-- Law of non-contradiction
-- AKA implication elimination
-- AKA function application
lnc : {A : Set} → A → (A → ⊥) → ⊥
lnc a a→⊥ = a→⊥ a

-- No RAA in a constructive proof
dne : {A : Set} → ((A → ⊥) → ⊥) → A
dne f = {!!} -- We need to manufacture an A, but we got none

-- No LEM in a constructive proof
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
lem : {A : Set} → A ⊎ (A → ⊥)
lem = {!!} -- To be or not to be demands a choice
\end{code}

Many variants exist on both sides of the isomorphism. The type theory
of simply typed lambda calculus — where $→$ is the only type
constructor — is in itself enough to model propositional logic. Type
theories containing dependent types — where the definition of a type
may depend on a value — model predicate logics containing quantifiers.

\begin{code}
-- Truth: a type with a single constructor trivial to satisfy
record ⊤ : Set where
  constructor tt
  
-- Natural numbers, defined inductively
data ℕ : Set where
  zero :     ℕ
  suc  : ℕ → ℕ
  
-- A predicate, or a proposition that depends on a value
Even : ℕ → Set
Even zero = ⊤
Even (suc zero) = ⊥
Even (suc (suc n)) = Even n

-- The type of t depends on the value n
half : (n : ℕ) → (t : Even n) → ℕ
half zero tt = zero
half (suc zero) ()  -- No t ∶ Even (suc zero)
half (suc (suc n)) t = suc (half n t)
\end{code}

Proofs should not suffer from the halting problem — they should be
rejected if they don't clearly show that they will eventually reach
termination. If we consider programs to be proofs, programs for which
termination cannot be verified should be rejected.

One way of showing termination is by always making recursive calls on
structurally smaller arguments. If data is defined inductively, this
assures that a base case is always eventually reached, and that
therefore recursion is always eventually terminating.

\begin{code}
-- The lowerscores show where the arguments go
_+_ : ℕ → ℕ → ℕ
zero + m = m            -- Base case of first argument
suc n + m = suc (n + m) -- First argument gets smaller

-- Would never terminate
-- nonsense : {!!} -- There is no type for it
-- nonsense = nonsense
\end{code}

\section{Reasoning in Agda}

Agda is a \textbf{purely functional} (no side-effects)
\textbf{dependently typed} (types contain values) \textbf{totally
defined} (functions must terminate and be defined for every possible
case) language based on Per Martin-Löf's intuitionistic type
theory. It was first developed by Catarina Coquand in 1999 and later
rewriten by Ulf Norell in 2007. \cite{Norell2009} is an excellent
introduction; more in-depth documentation can be found at
\cite{Agda}. This section will only briefly cover the basics required
to familiarise the reader with what theorem proving in Agda looks
like.

\subsection{The experience of programming in Agda}

Development in Agda happens inside Emacs, and is a two way
conversation between the compiler and the programmer. Wherever a
definition is required, the user may instead write $?$ and request the
type-checker to reload the file. A "hole" will appear where the $?$
was. The programmer can then:

\begin{itemize}[noitemsep]
  \item examine the type of the goal;
  \item examine the types of the values in context;
  \item examine the type of an arbitrary expression;
  \item pattern match on a type;
  \item supply a value, which may contain further holes;
  \item attempt to refine the goal; or
  \item attempt to automatically solve the goal.
\end{itemize}

This interactive way of programming, often described as "hole driven",
allows the programmer to work with partial definitions and to receive
constant feedback from the type-checker.

\subsection{A quick note on the syntax}

\todo{misfix, implicit arguments, multiple arguments same type, named
arguments, ∀}

\subsection{Datatypes and pattern matching}

Algebraic data types are introduced by the \AgdaKeyword{data}
keyword. They may contain multiple constructors, all of which must be
of the previously declared type.

\begin{code}
data Direction : Set where
  Up    : Direction
  Left  : Direction
  Down  : Direction
  Right : Direction
\end{code}

Constructors can accept arguments, which may be recursive:

\begin{code}
data Path : Set where
  start :                    Path
  walk  : Direction → Path → Path
\end{code}

Datatypes may accept parameters. If they do, every constructor in the
datatype has to have that same parameter in its return type. Hence
these parameters are named:

\begin{code}
data List (A : Set) : Set where
  []  :              List A
  _∷_ : A → List A → List A

Path' : Set
Path' = List Direction
\end{code}

Moreover, datatypes can be indexed. Each of these indices is said to
introduce a family of types. Constructors do not need to keep within
the same index, and may in fact \textit{jump} from one to
another. Parameters are forced on datatypes, but indices are a choice.

\begin{code}
-- Parametrised by A : Set, indexed by ℕ
data Vec (A : Set) : ℕ → Set where
  []  :                       Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

Path'' : ℕ → Set
Path'' = Vec Direction

stay-put : Path'' zero
stay-put = []
\end{code}

Whenever a datatype is pattern matched against, it will split into
those constructors capable of constructing that type:

\begin{code}
-- Vec A n matches both constructors
wrong-head : {A : Set}{n : ℕ} → Vec A n → A
wrong-head [] = {!!} -- There is no A
wrong-head (x ∷ xs) = x

-- Vec A (suc n) only matches _∷_
head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ∷ xs) = x
\end{code}

In Agda, pattern matching drives computation, and every case that is
result of it further refines the types in context.

\begin{code}
-- Note that xs, ys and the result have the same length
zipWith : {A B : Set}{n : ℕ} (f : A → A → B) (xs ys : Vec A n ) → Vec B n
--> zipWith f xs ys = {!!}
-- If xs was constructed with [], it has length zero
--> zipWith f [] ys = {!!}
-- If xs has length zero, so does ys
zipWith f [] [] = []
-- If xs was constructed with _∷_, it has length (suc n)
--> zipWith f (x ∷ xs) ys = {!!}
-- If xs has length (suc n), so does ys 
--> zipWith f (x ∷ xs) (y ∷ ys) = {!!}
-- And so does the result
--> zipWith f (x ∷ xs) (y ∷ ys) = {!!} ∷ {!!}
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys
\end{code}

\subsection{Views}

With abstraction gives the programmer the ability to steer unification
in a particular direction by allowing them to pattern match on
arbitrary well-formed expressions on the left hand side of a
definition. This may result in the remaining arguments being refined.

\begin{code}
\end{code}

\cite{Oury2008}

\subsection{Propositional equality}

Any two terms are considered propositionally equal if they unify with
each other:

\begin{code}
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
\end{code}

\AgdaRef{\_≡\_} is parametrised by an implicit type $A$ and a value $x
: A$ and indexed by a value in $A$. Given some fixed parameter $x$,
for every $y : A$ $x ≡ y$ is thus a type. The constructor
\AgdaRef{refl} is the only way of constructing a value of type $x ≡ y$
and crucially, it can only construct values where $x ≡ x$ after
normalisation.

\begin{code}
-- Computation of suc zero + suc zero happens at compile time
-- Both sides normalise to suc (suc zero)
1+1≡2 : (suc zero + suc zero) ≡ suc (suc zero)
1+1≡2 = refl

sym : {A : Set}{x y : A} → x ≡ y → y ≡ x
--> sym r = {!!}
-- r : x ≡ y
-- Goal : y ≡ x
--> sym refl = {!!} <-- We learn that x and y unify
-- Goal : x ≡ x
sym refl = refl
\end{code}

\subsection{Rewrites}

\begin{code}
{-# BUILTIN EQUALITY _≡_ #-} 
\end{code}

\subsection{Implementation matters}

One could think that proving $(n + zero) ≡ n$ is similar to proving
$(zero + n) ≡ n$, but it is not. Depending on whether \AgdaRef{\_+\_}
case splits on the first or on the second argument, one of those
proofs will be trivial while the other will require induction.

\begin{code}
-- zero + n immediately normalises to n
0+n≡n : (n : ℕ) → (zero + n) ≡ n
0+n≡n n = refl

-- n + zero cannot normalise:
-- Was n constructed with zero or with suc?
-- We need to use induction
n+0≡n : (n : ℕ) → (n + zero) ≡ n
n+0≡n zero = refl
n+0≡n (suc n) rewrite n+0≡n n = refl
\end{code}

\section{A comment on Agda-Stdlib}

\cite{AgdaStdlib}

\chapter{A solver for monoids}

It is not unlikely that while solving some bigger problem, one finds
out that part of it can be modeled as an equation on monoids, and thus
solved by a monoid solver.

A monoid is a set `M` together with:

\begin{itemize}
  \item a binary operation \(· : M → M → M\) that is associative:
    \[
    ∀ (x y z : M) → (x · y) · z ≡ x · (y · z)
    \]
  \item a neutral element \(ε : M\)
    \[
    ∀ (x : M) → ε · m ≡ m
    ∀ (x : M) → m · ε ≡ m
    \]
\end{itemize}

It is important to note that a monoid is not required to be
commutative. Examples of monoids are \((ℕ, +, 0)\), \((ℕ, ·, 1)\) and
\((∀ {T} → List T, ++, [])\).





With Agda and its dependent types, we can make the typechecker check such a proof, at compile time. Our solver is going to return something of type Solution :: Expression → Expression → Set.

Let P = ((0 + x) + (x + y)) and Q = ((x + x) + y). Then Solution P Q [code] will give back the type ∀ (x y) → P ≡ Q representing an equality proof between P and Q for all possible assignments. If both sides were not equivalent, we would get a Failure [code] or some other trivial type.

We can now define a function solve : (p : P) → (q : Q) → Solution p q [code]. This function has to give back either the actual equality proof on all possible assignments, or some trivial value indicating failure.

The monoid laws can be used to distill an expression’s essence: [code]

P = ((0 + x) + (x + y))  Q = ((x + x) + y)
-- Absorb all neutral elements
P = (x + (x + y))        Q = ((x + x) + y)
-- Associativity doesn't matter
P = x + x + y            Q = x + x + y
-- We don't get any information out of +, it's meaningless
-- Let's translate them into lists
P = x ∷ x ∷ y ∷ []       Q = x ∷ x ∷ y ∷ []

If these two lists are equal, then the expressions they came from must be equivalent. In other words: given any variable assignment, it doesn’t matter if we evaluate the original expressions [code] or the resulting lists [code], the result is the same. Translating them into lists (free monoids), we get rid of anything that makes two equivalent expressions constructively different.

Now we only need to prove to Agda that translating expressions into lists to then evaluate those and evaluating expressions is indeed equivalent. [code]

 Expr X --evalExpr----.  If
   |                  |  ∀ (e : Expr X) →
exprList              |  evalList (exprList e) ≡ evalExpr e
   |                  |  Then
   v                  v  ∀ (p q : Expr X) →
 List X --evalList--> M  exprList p ≡ exprList q ⇔ evalExpr p ≡ evalExpr q


- What is a Monoid?
- Canonical forms and evaluation homomorphism
- Lists are free monoids

\chapter{A solver for commutative rings}

- What is a commutative ring?
- Horner normal form + constraints

\chapter{A solver for Presburger arithmetic}

\chapter{Problem description and specification}

%   Problem Description and Specification Describe in detail, with examples if
%   appropriate, the problem which you are trying to solve. You should clearly
%   and concisely specify the problem and should say how the specification was
%   arrived at. You should also provide a general discussion of your approach to
%   solving the project problem.

- What Presburger arithmetic is
- The three ways of solving it
- What ways we chose, and why
- How to do this in Agda, what the benefits are

%   As part of this chapter – or more likely in a related appendix – you should
%   also normally include the original plan which was submitted as part of your
%   Project Specification and Plan deliverable in the first semester. You should
%   not, however, be particularly concerned if your project deviated slightly
%   from this plan.

\chapter{System design}

- Why Prelude
- High level plan of the module
    - Representation
    - Normalisation
    - Simplification
    - Correctness proofs
    - Quoting

%   System Design In this chapter, you should describe how the project was
%   designed. You should include discussions of the design method, design
%   process, and final design outcome. This is where you include the high level
%   description of the architecture of your project's product and, if
%   appropriate, the design of the user interface and data management.

\chapter{Detailed design and implementation}

%   Detailed Design and Implementation In this chapter you should describe your
%   design in more detail, taking the most interesting aspects right down to the
%   implementation details. You should include detailed design decisions and
%   trade-offs considered and made, such as the selection of algorithms, data
%   structures, implementation languages, and appropriate tools to support the
%   development process. It should also include your justifications for these
%   choices. In addition, you should describe how you have tried to address
%   relevant qualities of the product produced, such as maintainability,
%   reliability, and user-friendliness. It is not necessary to describe every
%   aspect of your system in excruciating detail, but you should describe each
%   in enough detail that the reader of your report can understand the overall
%   project, and you should thoroughly discuss the most demanding and
%   interesting aspects of your design and implementation.

\chapter{Verification and validation}

%   Verification and Validation In this section you should outline the
%   verification and validation procedures that you've adopted throughout the
%   project to ensure that the final product satisfies its specification. In
%   particular, you should outline the test procedures that you adopted during
%   and after implementation. Your aim here is to convince the reader that the
%   product has been thoroughly and appropriately verified. Detailed test
%   results should, however, form a separate appendix at the end of the report.

- Why is this absolutely correct, Agda?

\chapter{Results and evaluation}

%   Results and Evaluation The aim of this chapter is twofold. On one hand, it
%   aims to present the final outcome of the project – i.e., the system
%   developed – in an appropriate way so that readers of your report can form a
%   clear picture of the system operation and provided functionality without the
%   need for a live demo. This would normally require the inclusion of
%   screenshots and/or images of the system in operation, and indicative results
%   generated by the system. On the other hand, this chapter also aims to
%   present an appropriate evaluation of the project as whole, both in terms of
%   the outcome and in terms of the process followed.

%   The evaluation of the outcome is expected to be primarily evidence-based,
%   i.e., the result of either an experimental process, like usability tests and
%   evaluations, performance-related measurements, etc., or a formal analysis,
%   such as algorithmic and mathematical analysis of system properties, etc. The
%   precise nature of the evaluation will depend on the project requirements.
%   Please note that if you intend to carry out usability tests, you will need
%   to first obtain approval from the Department's Ethics Committee - the
%   section on Evaluation and Ethics Approval provides further detail.

%   The evaluation of the process is expected to be primarily a reflective
%   examination of the planning, organisation, implementation and evaluation of
%   the project. This will normally include the lessons learnt and explanations
%   of any significant deviations from the original project plan.

\chapter{Related work}

%   Related Work You should survey and critically evaluate other work which you
%   have read or otherwise considered in the general area of the project topic.
%   The aim here is to place your project work in the context of the related
%   work.

\chapter{Summary and conclusions}

%   Summary and Conclusions In the final chapter of your report, you should
%   summarise how successful you were in achieving the original project
%   objectives, what problems arose in the course of the project which could not
%   be readily solved in the time available, and how your work could be
%   developed in future to enhance its utility. It is OK to be upbeat,
%   especially if you are pleased with what you have achieved!

\bibliographystyle{alpha}
\bibliography{bibliography}

%   References/Bibliography The references should consist of a list of papers
%   and books referred to in the body of your report. These should be formatted
%   as for scholarly computer science publications. Most text- and word-
%   processors provide useful assistance with referencing - for example latex
%   uses bibtex. As you know, there are two principal reference schemes.

%       In one, the list is ordered alphabetically on author's surname and
%       within the text references take the form (Surname, Date). For example, a
%       reference to a 2014 work by Zobel would be written (Zobel, 2014).

%       In the other, the list is ordered in the sequence in which a reference
%       first appears in the report.

%   For both schemes, each reference in the reference list should contain the
%   following information: author, title, journal or publisher (if book), volume
%   and part, and date. Depending of the style of references you use, Zobel's
%   2014 book might be listed in the references of your report as follows:

%   Justin Zobel. Writing for Computer Science. Springer-Verlag, 2014.

%   For more examples of the first style, see the way in which references are
%   laid out in "Software Engineering: A Practitioner's Approach" by Roger
%   Pressman. Note carefully that your references should not just be a list of
%   URLs! Web pages are not scholarly publications. In particular, they are not
%   peer reviewed, and so could contain erroneous or inaccurate information.

\appendix

\chapter{Detailed Specification and Design}
%   Appendix A - Detailed Specification and Design This appendix should contain
%   the details of your project specification that were not included in the main
%   body of your report.

\chapter{Detailed Test Strategy and Test Cases}
%   Appendix B - Detailed Test Strategy and Test Cases This appendix should
%   contain the details of the strategy you used to test your software, together
%   with your tabulated and commented test results.

\chapter{User Guide}
%   Appendix C - User Guide This appendix should provide a detailed description
%   of how to use your system. In some cases, it may also be appropriate to
%   include a second guide dealing with maintenance and updating issues.

\end{document}
