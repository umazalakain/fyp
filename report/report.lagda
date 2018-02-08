\documentclass[12pt,a4paper]{scrreprt}

\usepackage[english]{babel}

% Links inside the bibliography
\usepackage{hyperref}

\usepackage{agda}[conor]
% \setmathfont{texgyreschola-math.otf}

\usepackage{fullpage}

\begin{document}
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
\end{abstract}

\section*{Acknowledgements}

\tableofcontents

- Proving certain theorems can be boring and we want to automate it
- We don't want just the answer, we want a proof that it is the correct answer

\chapter{Introduction}

%   Introduction This should briefly describe the problem which you
%   set out to solve and should essentially summarise the rest of your
%   report. The aim of an introduction is to convince the reader that
%   they should read on, so it is very important that excessive detail
%   is avoided at this stage.

Formal proofs construct theorems by sequentially applying the axioms
of a formal system. Computers can assist this process and make theorem
proving a conversation between the mathematician and the computer,
which continually checks the correctness of the proof. Yet, theorem
proving can often be boring and tedious: certain theorems are trivial
or uninteresting but require many rewrites.

It is in those cases where automated theorem proving shines
strongest: instead of applying inference rules manually, the user
provides the automated theorem prover with a proposition and gets a
verified answer back. This verification can come from outside of the
decision procedure — as a proof of its correctness — or from inside it
— in the form of a witness or proof. Furthermore, these decision
procedures are often based on some meta-theory about the system, and
thus can result in less rewriting steps than the blind application of
inference rules from inside the system.

For a computer to verify the proof for some proposition, there must
exist some computational model for both proofs and propositions. One
was first discovered by Haskell Curry and later strengthened by
William Alvin Howard, and it establishes a two way correspondence
between type theory and constructive logic: propositions are types and
proofs are programs; to prove a proposition is to construct a program
inhabiting certain type. A type-checker is now suddenly capable of
verifying proofs.

\begin{code}
-- Falsehood: an uninhabited type with no constructors
data ⊥ : Set where

-- Ex falso quodlibet
-- Agda can see there is no way of constructing ⊥
-- There is no need to provide a case for when that happens
explosion : {A : Set} → ⊥ → A
explosion ()

-- Truth : a type with a trivial constructor
record ⊤ : Set where
  constructor tt

-- Proving truth is trivial
trivial : ⊤
trivial = tt
\end{code}

Many variants exist on both sides of the isomorphism. The type theory
of simply typed lambda calculus — where $→$ is the only type
constructor — is in itself enough to model propositional logic. Type
theories containing dependent types, where the definition of a type
may depend on a value, model predicate logics containing quantifiers.

\begin{code}
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

data ℕ : Set where
  zero :     ℕ
  suc  : ℕ → ℕ
  
NonZero : ℕ → Set
NonZero zero = ⊥
NonZero (suc n) = ⊤

-- NonZero (suc n) computes to ⊤
one-is-non-zero : Σ ℕ NonZero
one-is-non-zero = suc zero , tt

-- NonZero zero computes to ⊥
-- zero-is-not-non-zero : Σ ℕ NonZero
-- zero-is-not-non-zero = zero , ?
\end{code}

Type-checking — that is, proof verification — should be decidable and
terminating. If type-checking involves executing functions, these
functions have to be:

\begin{itemize}
  \item purely functional;
  \item defined for all of their domain; and
  \item guaranteed to terminate.
\end{itemize}

The termination guarantee can be achieved by requiring recursive calls
to happen on structurally smaller arguments. If data is defined
inductively, this assures that a base case will be eventually reached,
and therefore that recursion will terminate.

\begin{code}
_+_ : ℕ → ℕ → ℕ
-- Base case of second argument
n + zero = n
-- Second argument gets smaller
n + suc m = suc (n + m)

-- No inductively defined data type decreasing in size
-- nonsense : ?
-- nonsense = nonsense
\end{code}


- What Agda is
- How Agda works as a proof assistant
- Presburger arithmetic as an interesting goal

%   The introduction should include the list of objectives that you identified
%   for the project, as well as a brief overview of the outcome. In its final
%   part, the introduction will usually outline the structure of the rest of the
%   report.

- Better understand theorem proving in Agda
- Write something that can be useful for others to use

\chapter{Related work}

%   Related Work You should survey and critically evaluate other work which you
%   have read or otherwise considered in the general area of the project topic.
%   The aim here is to place your project work in the context of the related
%   work.

Before we start trying to envisage a solution to our main challenge — writing a
solver for Presburger arithmetic in Agda —, it is sensible to consider and
implement easier, yet non-trivial problems. We will look at two distinct
solvers, both of them solvers for algebraic structures.

\subsection{Monoid solver}

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

\subsection{Commutative ring solver}

- What is a commutative ring?
- Horner normal form + constraints

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

- The source code itself, minus the boring bits
- Things from agda-stdlib in the abstract?

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

\chapter{Summary and conclusions}

%   Summary and Conclusions In the final chapter of your report, you should
%   summarise how successful you were in achieving the original project
%   objectives, what problems arose in the course of the project which could not
%   be readily solved in the time available, and how your work could be
%   developed in future to enhance its utility. It is OK to be upbeat,
%   especially if you are pleased with what you have achieved!

\chapter{Bibliography}

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

\bibliographystyle{alpha}
\bibliography{bibliography}

\end{document}
