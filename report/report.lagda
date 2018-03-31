\documentclass[12pt,a4paper,abstract=on,bibliography=openstyle,bibliography=totoc]{scrreprt}

\usepackage[english]{babel}

% Equations
\usepackage{amsmath}

% Theorems
\usepackage{amsthm}
\newtheorem{theorem}{Theorem}

% Break urls
\usepackage[T1,hyphens]{url}

% Links and their colors
\usepackage[
  colorlinks=true,
  linkcolor=darkgray,
  citecolor=darkgray,
  urlcolor=darkgray,
  ]{hyperref}

% And fonts
\urlstyle{rm}

% Type checking for Agda
\usepackage[conor,references]{agda}

% Use DejaVu Math for all code
\setmathsf{DejaVu Math TeX Gyre}
\setmathfont{DejaVu Math TeX Gyre}
\everymath{\scriptstyle}

% Avoid having variables in italics
\renewcommand{\AgdaBoundFontStyle}[1]{\ensuremath{\mathsf{#1}}}

% XITS doesn't have small caps
\setmainfont[
  Ligatures=TeX,
  SmallCapsFont={TeX Gyre Termes},
  SmallCapsFeatures={Letters=SmallCaps},
]{XITS}

% List customization
\usepackage[inline]{enumitem}

% They are all over the place
\usepackage{todonotes}

% Two columns in the title page
\usepackage{multicol}

% And an image too
\usepackage{graphicx}

% Footnote symbols
\renewcommand{\thefootnote}{\fnsymbol{footnote}}

% Diagrams
\usepackage{tikz}
\usetikzlibrary{arrows,positioning}

% Appendices
\usepackage[header,title,titletoc]{appendix}
\renewcommand{\appendixname}{Appendix}

% Include parts of other files
\usepackage{catchfilebetweentags}

% Intertext with less vertical space
\usepackage{mathtools}

% License
\usepackage[
    type={CC},
    modifier={by-sa},
    version={3.0},
]{doclicense}

\begin{document}

% Always use § for references to document structures
\renewcommand{\chapterautorefname}{\S}
\renewcommand{\sectionautorefname}{\S}
\renewcommand{\subsectionautorefname}{\S}
\renewcommand{\subsubsectionautorefname}{\S}

\AgdaHide{
\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module _ where
\end{code}}

\begin{titlepage}
    {
        \centering
        \scshape

        Submitted for the Degree of B.Sc. in Computer Science, 2017-2018

        \rule{\textwidth}{1.6pt}
        \vspace{0mm}

        {\Huge Evidence providing\\ problem solvers\\ in Agda\\}

        \vspace{8mm}
        \rule{\textwidth}{1.6pt}

        \vfill
        \includegraphics[width=4cm]{chi.png}
        \footnote{The Curry-Howard homeomorphism, by Luca Cardelli, adapted by Iune Trecet}
        \vfill

        \begin{multicols}{2}
            {\raggedright{}
                {\scriptsize 201434138}\\
                {\Large Uma Zalakain}\\
            }
            \columnbreak
            {\raggedleft{}
                {\small Supervised by}\\
                {\Large Conor McBride}\\
            }
        \end{multicols}
        \vspace{1cm}
    }

    {\raggedleft{}
    Except where explicitly stated all the work in this report,
    including appendices, is my own and was carried out during my
    final year. It has not been submitted for assessment in any other
    context. I agree to this material being made available in whole or
    in part to benefit the education of future students.
    }
    \vspace{1cm}
\end{titlepage}


\newpage

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{abstract}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

The Curry-Howard correspondence draws a direct link between logic and
computation: propositions are modelled as types and proofs as
programs; to prove a proposition is to construct a program inhabiting
its corresponding type. Several computer-assisted theorem provers have
been developed under this idea. They are not just used to verify human
reasoning: they are also often capable of generating proofs
automatically.

This project considers the development of such automated theorem
provers in Agda, a dependently typed programming language. As a
warm-up, I present a verified solver for equations on monoids. Then, I
comment on the solver for commutative rings included in Agda's
standard library. Finally, I develop a verified decision procedure for
Presburger arithmetic — a decidable first-order predicate logic.

\end{abstract}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section*{Acknowledgements}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This project is an attempt to distill all the support, attention,
knowledge, dedication and love I was given into concrete ideas in
printable format. Despite the disclaimer saying otherwise, this
project is far from being just my own work. At least a dozen people
have contributed to it, either unknowingly, directly, or by
contributing to my well-being.

My supervisor has been a key figure, first as the lecturer of the 12
week introduction to Agda I was lucky to receive, then as a supervisor
who has a keen interest in the subject and is willing to share
it. This project was the perfect excuse for countless hours of
education.

Frustration, loneliness, self-doubt, dysphoria and my neighbour's
barking dog have played the role of evil creatures of the darkness,
and deserve to be acknowledged. Luckily for me, my friends, both local
and remote, and my parents, on the other side of this planet, gave me
enough resolution to shed some bright light on them. And my
neighbour's dog, along with their owner, finally moved away.

Needless to say, this project, of little importance to anyone but me,
is based on large amounts of previous science and countless hours of
accumulated human effort. To all those people who have kept the candle
burning, I am forever grateful.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% License
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\vfill{}
\doclicenseThis

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TOC
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\tableofcontents

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Introduction}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Formal proofs construct theorems by applying the rules of a formal
system. Computers can assist this process and make theorem proving a
conversation between the human and the computer, which checks the
correctness of their proof. Yet, theorem proving can often be boring
and tedious: certain theorems are trivial or uninteresting but require
many steps.

It is in these cases where automated theorem proving shines strongest:
instead of applying inference rules manually, the user can provide an
automated solver with a proposition and get a verified solution
back. These decision procedures are often based on some meta-theory
about the system, and thus can result in less rewriting steps than the
repeated application of inference rules from inside the system.

The four color theorem was the first notable problem to be solved with
the help of a computer program. Since 1976, there remained doubts of
the correctness of such program until in 2005 Georges Gonthier used a
proof assistant to prove the theorem.

This project embarks upon constructing verified problem solvers.
Three different problems are considered: the first two involve solving
equalities on algebraic structures; the third deciding a first-order
predicate logic — Presburger arithmetic. The aim is to better
understand automated theorem proving as seen through the Curry-Howard
lens.

\autoref{ch:background} provides a brief introduction to the
relationship between machine programs and formal proofs, illustrated
with accompainying Agda programs. The chapter includes a short
introduction to programming in Agda, and establishes some of the base
ground required for formal verification.

\autoref{ch:monoids} starts with a simple example: a verified solver
for equations on monoids. \autoref{ch:rings} comments on a more
involved solver for commutative rings found in Agda's standard
library. This project then culminates with \autoref{ch:presburger},
where the heart of a Presburger arithmetic solver written in Agda is
presented. With some additional work, I am optimistic of its inclusion
into Agda's standard library.

Concluding, \autoref{ch:verification} reiterates the correctness that
the precision of dependently typed specifications is able to express,
and \autoref{ch:evaluation} and \autoref{ch:conclusion} contain
meta-analyses of the project's development process.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Background}
\label{ch:background}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This chapter starts by briefly introducing the case behind the use of
type-checkers as theorem verifiers. Next, a succint primer on
programming in Agda is given. In itself, such introduction is probably
not sufficient to get the unexperienced reader entirely comfortable
reading Agda code. Only more in-depth reading and hands-on practice
are likely to achieve that. Nevertheless, it is my hope that it
facilitates enough understanding to intuitively grasp some of the
ideas put forward in later sections of this report.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Proofs as programs; propositions as types}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

If a computer is to verify the proof of some proposition, some
computational model relating proofs and propositions must exist. One
such model was first devised by Haskell Curry \cite{Curry1934} and
later strengthened by William Alvin Howard \cite{Howard1980a}. It
establishes a two way correspondence between type theory and
constructive logic: propositions are isomorphic to types and proofs
are to programs; to prove a proposition is to construct a program
inhabiting its corresponding type; a proposition is not proven unless
a program of the corresponding type is given. Type-checkers can verify
formal proofs.

Ignoring — for now — all details specific to Agda, here are some
examples relating types to logical propositions: 

\AgdaHide{
\begin{code}
module _ where
  private
\end{code}
}

\begin{code}
    -- Truth: a type with a single constructor trivial to satisfy
    record ⊤ : Set where
        constructor tt

    -- Falsehood: an uninhabited type with no constructors
    data ⊥ : Set where

    -- Disjunction, with two constructors
    data _⊎_ (A B : Set) : Set where
      inj₁ : A → A ⊎ B
      inj₂ : B → A ⊎ B

    module Laws {A : Set} where
      -- ⊥ is an initial object: from it, anything can be produced
      -- There is no constructor for ⊥, pattern matching on the
      -- argument renders the case absurd
      explosion : ⊥ → A
      explosion ()

      -- Law of non-contradiction
      -- AKA implication elimination
      -- AKA function application
      lnc : A → (A → ⊥) → ⊥
      lnc a a→⊥ = a→⊥ a

      -- No proof by contradiction in constructive mathematics
      -- A witness in A is needed, but there is none
      dne : ((A → ⊥) → ⊥) → A
      dne f = {!!} 

      -- No law of excluded middle in constructive mathematics
      -- To be or not to be demands a choice
      -- Decidability is not universal
      lem : A ⊎ (A → ⊥)
      lem = {!!} 
\end{code}

Many variants exist on both sides of the isomorphism. The type theory
of simply typed lambda calculus — where $→$ is the only type
constructor — is in itself enough to model propositional logic. Type
theories with dependent types — where the definition of a type may
depend on a value — model predicate logics that contain quantifiers.
\cite{Sorensen2006d} is an comprehensive introduction to these ideas.

\begin{code}
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
rejected if they don't clearly show that they eventually reach
termination. If programs are considered to be proofs, programs for
which termination cannot be verified must be rejected.

One way of showing termination is by making recursive calls on
structurally smaller arguments. If data is defined inductively, this
assures that a base case is always eventually reached, and that
therefore recursion always eventually terminates.

\begin{code}
    _+_ : ℕ → ℕ → ℕ
    zero + m = m            -- Base case of first argument
    suc n + m = suc (n + m) -- First argument gets smaller

    -- Would never terminate
    -- nonsense : {!!}
    -- nonsense = nonsense
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Reasoning in Agda}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Agda is a \textbf{purely functional} (no side-effects)
\textbf{dependently typed} (types contain values) \textbf{totally
defined} (functions must terminate and be defined for every possible
case) language based on Per Martin-Löf's intuitionistic type
theory. It was first developed by Catarina Coquand in 1999 and later
rewriten by Ulf Norell in 2007. It compiles to multiple languages, but
Haskell is regarded as its main backend. \cite{Norell2009} is an
excellent introduction to Agda; technical documentation can be found
at \url{https://agda.readthedocs.io}. This section briefly covers the
basics of what theorem proving in Agda looks like and, in the spirit
of a tutorial, ocasionally uses the second person to avoid verbose
references to some third person programmer.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{The experience of programming in Agda}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Development in Agda happens inside Emacs, and is a two way
conversation between the compiler and you. Wherever a definition is
required, you may instead write $?$ and request the type-checker to
reload the file. A ``hole'' will appear where the $?$ was. You can
then:

\begin{itemize}[noitemsep]
  \item examine the type of that goal;
  \item examine the types of the values in context;
  \item examine the type of any arbitrary expression;
  \item pattern match on a type;
  \item supply a value, possibly containing further holes;
  \item attempt to refine the goal; or
  \item attempt to solve the goal automatically.
\end{itemize}

This interactive way of programming is often described as ``hole
driven''. Type-checking definitions before they writing them down
promotes the construction of well-formed expressions — instead of the
construction and subsequent debugging of malformed ones. Allowing holes
in those definitions makes the development model realistic.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Some peculiarities}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

For subsequent arguments to depend on it, an argument must be named.
If an argument can be inferred by the type-checker, you may choose to
make it implicit by naming it inside enclosing curly braces. Implicit
arguments can later still be explicitly provided and pattern matched
against. If the type of an argument can be inferred by the
type-checker, you may omit it and use $∀$:

\begin{code}
    -- All numbers are either even or not even
    prf₁ : ∀ {n} → Even n ⊎ (Even n → ⊥)
    prf₁ {zero} = inj₁ tt
    prf₁ {suc zero} = inj₂ λ b → b
    prf₁ {suc (suc n)} = prf₁ {n}
\end{code}

Multiple arguments sharing the same type can be grouped by giving
using multiple names. With the exception of whitespace and a few
special symbols, names in Agda may contain arbitrary unicode
symbols. In addition, names can use underscores as placeholders for
their arguments.

\begin{code}
    ∣_-_∣ : (x y : ℕ) → ℕ
    ∣ zero - y ∣ = y
    ∣ suc x - zero ∣ = suc x
    ∣ suc x - suc y ∣ = ∣ x - y ∣
\end{code}

An anonymous function can be provided where a function is
expected. You can pattern match against its arguments by wrapping the
arguments and body in curly brances.

\begin{code}
    pred : ℕ → ℕ
    pred = λ { zero    → zero
            ; (suc n) → n
            }
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Datatypes and pattern matching}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Algebraic data types are introduced by the \AgdaKeyword{data}
keyword. They may contain multiple constructors, all of which must be
of the declared type.

\begin{code}
    data Bool : Set where
      true  : Bool
      false : Bool
\end{code}

Constructors can accept arguments, which may be recursive:

\begin{code}
    data Bools : Set where
      []  :                Bools
      _∷_ : Bool → Bools → Bools
\end{code}

Datatypes may accept parameters. If they do, every constructor in the
datatype has to have that same parameter in its return type. Hence
these parameters need to be named:

\begin{code}
    data List (A : Set) : Set where
      []  :              List A
      _∷_ : A → List A → List A
\end{code}

Data types with a single constructor can be defined as records.
Bellow, a record type where the type of one of the fields
depends on the value of the other:

\begin{code}
    record Σ (A : Set) (B : A → Set) : Set where
      constructor _,_
      field
        proj₁ : A
        proj₂ : B proj₁
\end{code}

Datatypes can be indexed. Each of these indices is said to introduce a
family of types. Constructors do not need to keep within the same
index, and may in fact \textit{jump} from one to another. Parameters
are forced on datatypes, but indices are a choice.

\begin{code}
    -- Parametrised by A : Set, indexed by ℕ
    data Vec (A : Set) : ℕ → Set where
        []  :                       Vec A zero
        _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
\end{code}

Pattern matching deconstructs a type, which creates one case per every
constructor capable of constructing that type:

\begin{code}
    -- Both constructors match Vec A n
    map : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
    map f [] = []
    map f (x ∷ xs) = f x ∷ map f xs

    -- Only matches _∷_ matches Vec A (suc n)
    head : {A : Set}{n : ℕ} → Vec A (suc n) → A
    head (x ∷ xs) = x
\end{code}

Computation is advanced by pattern matching. The RHS of each pattern
match case will have the type of the terms in its context refined by
the information obtained from the LHS.

\begin{code}
    -- Note that xs, ys and the result have the same length
    zipWith : {A B C : Set}{n : ℕ} (f : A → B → C) → Vec A n → Vec B n → Vec C n
    -- zipWith f xs ys = {!!}
    -- -- If xs was constructed with [], it has length zero
    -- zipWith f [] ys = {!!}
    -- -- If xs has length zero, so does ys
    -- zipWith f [] [] = {!!}
    -- -- And so does the result
    zipWith f [] [] = []
    -- -- If xs was constructed with _∷_, it has length (suc n)
    -- zipWith f (x ∷ xs) ys = {!!}
    -- -- If xs has length (suc n), so does ys 
    -- zipWith f (x ∷ xs) (y ∷ ys) = {!!}
    -- -- And so does the result
    -- zipWith f (x ∷ xs) (y ∷ ys) = {!!} ∷ {!!}
    zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys
\end{code}

If a type has no constructors capable of constructing it, the
type-checker will recognise the case as absurd and no definition will
be required on the RHS. This, together with the precision that
dependent types grant, makes handling erroneous input unecessary.

\begin{code}
    -- The successor of an even number cannot be even
    prf₂ : ∀ n → {p : Even n} → Even (suc n) → ⊥
    prf₂ zero {p} ()
    prf₂ (suc zero) {()} sp
    prf₂ (suc (suc n)) {p} sp = prf₂ n {p} sp 
\end{code}

If pattern matching against a type uniquely implies the constructor of
some other argument, the type-checker will substitute the argument by
the value preceded by a dot. If a term on the RHS can be inferred by
the type-checker, you may replace it by an underscore. Additionally,
underscores can be used as non-binded catch-alls on the LHS of a
definition.

\begin{code}
    -- Pattern matching on xs determines n
    zipWith' : {A B C : Set} (n : ℕ) (f : A → B → C) → Vec A n → Vec B n → Vec C n
    zipWith' .zero f [] [] = []
    zipWith' .(suc _) f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith' _ f xs ys
\end{code}

``With abstraction'' allows you to pattern match on the LHS against
arbitrary computations. This is often used to refine the rest of the
arguments and then perform further pattern matching on them. The
following example is adapted from the standard library and was
originally presented in \cite{McBride2004}:

\begin{code}
    -- Ordering n m is a proof…
    data Ordering : ℕ → ℕ → Set where
      less    : ∀ m k → Ordering m (suc (m + k))
      equal   : ∀ m   → Ordering m m
      greater : ∀ m k → Ordering (suc (m + k)) m

    -- …that can be generated for any two numbers
    compare : ∀ m n → Ordering m n
    compare zero    zero    = equal   zero
    compare (suc m) zero    = greater zero m
    compare zero    (suc n) = less    zero n
    compare (suc m) (suc n) with compare m n
    compare (suc .m)           (suc .(suc m + k)) | less    m k = less    (suc m) k
    compare (suc .m)           (suc .m)           | equal   m   = equal   (suc m)
    compare (suc .(suc m + k)) (suc .m)           | greater m k = greater (suc m) k
\end{code}

As a result of pattern matching
on \AgdaFunction{compare}~\AgdaBound{m}~\AgdaBound{n} you learn about
\AgdaBound{m} and \AgdaBound{n}. This is the key difference between
with abstraction and ordinary case splitting on the right hand
side. \cite{Oury2008} contains other interesting examples of views.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Intensional equality}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Intensional equality judges two terms equal based on how they were
constructed. Two terms with identical behaviour but of different
construction are considered different.

\AgdaHide{
\begin{code}
    module _ where
      private
\end{code}
}

\begin{code}
        data _≡_ {A : Set} (x : A) : A → Set where
          refl : x ≡ x
\end{code}

\AgdaHide{
\begin{code}
    open import Agda.Builtin.Equality
\end{code}
}

In ~\AgdaBound{x}~\AgdaRef{≡}~\AgdaBound{y}, ~\AgdaBound{x}~ is the
parameter and ~\AgdaBound{y}~ the index. The single constructor
~\AgdaRef{refl}~ constructs types where the parameter ~\AgdaBound{x}~
is provided as the index. This means that for
~\AgdaBound{x}~\AgdaRef{≡}~\AgdaBound{y}~ to be well-formed, Agda has
to be able to unify ~\AgdaBound{x}~ and ~\AgdaBound{y}: once both
terms are normalised into a tree of constructors, they must be
syntactically equal.

\begin{code}
    -- Both sides normalise to suc (suc zero)
    prf₃ : (suc zero + suc zero) ≡ suc (suc zero)
    prf₃ = refl
\end{code}

You can now start writing functions that compute proofs that involve
equality:

\begin{code}
    -- zero + n immediately normalises to n
    prf₄ : ∀ n → (zero + n) ≡ n
    prf₄ n = refl
\end{code}

However, not all equations immediately unify. Consider the following:

\begin{code}
    prf₅ : ∀ n → (n + zero) ≡ n
\end{code}

\AgdaBound{n} \AgdaFunction{+} \AgdaRef{zero} cannot normalise: as a
consequence of the definition of \AgdaRef{\_+\_}, it needs to be known
whether \AgdaBound{n} was constructed with \AgdaRef{zero} or
\AgdaRef{suc}. The computation can be advanced by pattern matching
on \AgdaBound{n}. While the base case is now trivial
(\AgdaRef{zero}~\AgdaFunction{+}~\AgdaRef{zero} unifies with
\AgdaRef{zero}), the problem persists in the inductive case, where
\AgdaRef{suc}~\AgdaSymbol{(}\AgdaBound{n}~\AgdaFunction{+}~\AgdaRef{zero}\AgdaSymbol{)}
has to unify with \AgdaRef{suc}~\AgdaBound{n}. By recursing on the
inductive hypothesis and on the subject of such hypothesis,
\AgdaBound{n}~\AgdaFunction{+}~\AgdaRef{zero} and \AgdaBound{n} can be
unified:

\begin{code}
    prf₅ zero = refl
    prf₅ (suc n) with n + zero | prf₅ n
    prf₅ (suc n) | .n          | refl = refl
\end{code}

This recursion on the induction hypothesis is common enough that
special syntax exists for it:

\begin{code}
    prf₆ : ∀ n → (n + zero) ≡ n
    prf₆ zero = refl
    prf₆ (suc n) rewrite prf₆ n = refl
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{The inspect idiom}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\todo{inspect}

% -- The inspect idiom can be used when you want to pattern match on
% -- the result r of some expression e, and you also need to
% -- "remember" that r ≡ e.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Tools for reasoning}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

To aid reasoning, tools that enable whiteboard-style deductions have
been developed. These functions exploit the transitivity of the binary
relation they are defined for — may it be equality or other preorder
relations like $≤$ or $⇒$. This style of reasoning, together with the
congruent property of functions, is used profusely throught this
report.

\AgdaHide{
\begin{code}
    open import Relation.Binary.PropositionalEquality using ()
    open Relation.Binary.PropositionalEquality.≡-Reasoning
\end{code}}

\begin{code}
    cong : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
    cong f refl = refl
\end{code}

\begin{code}
    prf₇ : ∀ l n m → ((zero + (l + zero)) + (n + zero)) + m ≡ (l + n) + m
    prf₇ l n m = begin
      ((zero + (l + zero)) + (n + zero)) + m
        ≡⟨⟩ -- Needs no justification, both types immediately unify
      ((l + zero) + (n + zero)) + m
        ≡⟨ cong (λ ● → (● + (n + zero)) + m) (prf₆ l) ⟩
      (l + (n + zero)) + m
        ≡⟨ cong (λ ● → (l + ●) + m) (prf₆ n) ⟩
      (l + n) + m
        ∎ 
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Proof by reflection}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Procedures that try to automatically solve goals require some
notion of what their target theorem is. To prove the goal within Agda,
this notion has to be manipulated and inspected by pattern
matching. To do so, it needs to be translated into an inductive data
type — this process is often called \textit{metaification} or
\textit{reflection}. Both \cite{Gregoire2005} and \cite{Boutin1997}
introduce this idea.

This is in contrast with proof assistants like Coq, which often supply
externally defined ``tactics''; in Agda, automated theorem provers
are defined within the system.

\href{https://agda.readthedocs.io/en/latest/language/reflection.html}{
The support for reflection offered by Agda} gives the programmer the
ability to ``quote'' arbitrary parts of the program into abstract
terms representing them. In the other direction, these abstract terms
can be procedurally built and later ``unquoted'' into concrete Agda
code. Additionally, Agda also offers means to directly control type
checking and unification.

Agda's reflection mechanism is most commonly used to satisfy proof
goals automatically. For this common use case, Agda provides
``macros'': functions that take their target quoted goal as an
argument and hand back some computation solving it.

The next example from Agda's documentation shows how the macro
~\AgdaFunction{by-magic}~ uses ~\AgdaFunction{magic}~ to construct
values of a given type. Note that ~\AgdaFunction{magic}~ returns a
~\AgdaDatatype{Term}~ inside a ~\AgdaDatatype{TC}~ monad: this allows
~\AgdaFunction{magic}~ to throw type errors with custom error
messages.

\AgdaHide{
\begin{code}
module _ where
  private
    open import Agda.Builtin.Unit
    open import Agda.Builtin.Reflection
\end{code}
}

\begin{code}
    postulate magic : Type → TC Term

    macro
      by-magic : Term → TC ⊤
      by-magic hole =
        bindTC (inferType hole) λ goal →
        bindTC (magic goal) λ solution →
        unify hole solution
\end{code}

Both \cite{Walt2012} and \cite{VanDerWalt2012} are in-depth
introductions to Agda's reflection mechanism and come supplemented
with examples. \cite{Kokke2015} uses reflection to, given a list of
hints, conduct automatic first-order proof search on a goal type.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Builtins, Stdlib and Prelude}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Agda is distributed together with a
\href{https://agda.readthedocs.io/en/latest/language/built-ins.html}{set
of builtin data types and functions} found under the
\AgdaModule{Agda.Builtin}~module. These builtins are then referenced
by a set of directives (or \textit{pragmas}), so that Agda can, for
instance, translate numerical literals into terms of type
~\AgdaDatatype{ℕ}. \AgdaModule{Agda.Builtin}~does not provide
any proofs of the properties related to its data types.

The development of
\href{https://github.com/agda/Agda-Stdlib}{Agda-Stdlib} happens in
close coordination to Agda's. Unlike \AgdaModule{Agda.Builtin}'s
conservative approach, Agda-Stdlib provides a large library of
commonly used data structures and functions. It abstracts aggressively
which, together with its heavy use of unicode symbols and infix
notation, can often result in code challenging to read for the
unexperienced user. It contains a rather vast set of already proven
theorems for all of its data types.

In comparison,
\href{https://github.com/ulfnorell/agda-prelude}{Agda-Prelude} is less
abstract and more readable and efficient, but by far not as complete.

This project uses Agda-Stdlib as its sole dependency.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Miscellanea}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\subsubsection{Universes}

To avoid Russell's paradox, Agda introduces a hierarchy of universes
~\AgdaPrimitiveType{Set}~\AgdaSymbol{:}~\AgdaPrimitiveType{Set₁}~\AgdaSymbol{:}~\AgdaPrimitiveType{Set₂}\ldots~
where ~\AgdaPrimitiveType{Set}~ is the type of all small types like
~\AgdaDatatype{Bool}~ or ~\AgdaDatatype{ℕ}.

\subsubsection{Postulates and safe mode}

In Agda, any proposition can be introduced as a postulate. Some
postulates can lead to inconsistencies:

\AgdaHide{
\begin{code}
    open import Data.Sum using (_⊎_ ; inj₁)
    open import Data.Unit using (tt)
    open import Data.Empty using (⊥)
\end{code}}

\begin{code}
    postulate ¬LEM : {A : Set} → A ⊎ (A → ⊥) → ⊥
    LEM : {A : Set} → A ⊎ (A → ⊥)
    LEM with ¬LEM (inj₁ tt)
    LEM | () 
\end{code}

Executing Agda with the \texttt{{-}{-}safe} switch deactivates those
features that may lead to inconsistencies, like postulates, accepting
unsolved proofs or
~\AgdaPrimitiveType{Set}~\AgdaSymbol{:}~\AgdaPrimitiveType{Set}.
Unfortunately, Agda's standard library does not quarentine unsafe
definitions, so any module that depends on it is considered unsafe too
— albeit not using any of its unsafe features. There is
\href{https://github.com/agda/agda-stdlib/issues/143}{work in
progress} to address that.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Problem solvers and their domains}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This report presents evidence providing problem solvers for three
distinct domains — namely monoids, commutative rings, and Presburger
arithmetic. The background and the work related to each of these
domains is relevant only to itself. For that reason, and because I
judge it beneficial to have those introductory sections close to the
work that depends on them, I present the background of each problem
inside its dedicated chapter.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Solving monoids}
\label{ch:monoids}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Monoids are common algebraic structures found in many problems. A
monoid solver is an procedure that automatically generates a proof of
the equality of two monoids. Constructing such a solver is a good
first approach to proof automation: it lacks the complexity of many
other problems but still has their same high-level structure.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Problem description and specification}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\href{https://agda.github.io/agda-stdlib/Algebra.html#1079}{Agda-Stdlib's
definition of a monoid} is based on notions about many other algebraic
structures, and is therefore fairly complex. Instead, I present a
self-contained and fairly simple definition:

\ExecuteMetaData[Monoids.tex]{monoid}

\AgdaBound{M}, the set on which the monoid is defined, is often referred
to as the carrier. $(ℕ, +, 0)$ and $(ℕ, ·, 1)$ are both examples of
monoids. These examples also happen to be commutative, while monoids
need not be — more on solving commutative monoids later. An example of
a non-commutative monoid are lists together with the concatenation
operation:

\ExecuteMetaData[Monoids.tex]{list-monoid}

An equation on monoids cannot be decided by unification alone: the
monoid laws show that definitionally distinct propositions might in
fact have the same meaning.

\ExecuteMetaData[Monoids.tex]{eqn1}

Without an automated solver, the number of law applications and hence
the length of the proof grows with respect to the size of the term. An
automated solver should allow to effortlessly satisfy a proposition
like the following:

\ExecuteMetaData[Monoids.tex]{eqn2}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{A verified decision procedure}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

A proposition containing variables and monoid operators can be
normalised into a canonical form. The characteristics that make two
propositions definitionally distinct — when they are equal modulo the
monoid axioms — can be eliminated. It is crucial that this process —
normalisation — guarantees the preservation of meaning. After
normalisation, two results can be compared: if they are equal, so must
the original expressions be. This is the sketch of the decision
procedure.

I use an abstract syntax tree to represent equations and finite
indices to refer to variables — the type
\AgdaDatatype{Fin}~\AgdaBound{n} contains \AgdaBound{n} distinct
values. Moreover, I use a type parameter on ~\AgdaDatatype{Eqn}~ to
\textit{push in} this limitation on the number of indices.

\ExecuteMetaData[Monoids.tex]{expr}

Consider the following two expressions:

\begin{align*}
    P &= ((ε · x) · (x · y))  &  Q &= ((x · x) · y) \\
    \intertext{Neutral elements do not have any meaning and can be
    absorbed:}
    P &= (x · (x · y))        &  Q &= ((x · x) · y) \\
    \intertext{Elements can always be re-associated: association does
    not have any meaning and can be removed:}
    P &= x · x · y            &  Q &= x · x · y     \\
\end{align*}
Both propositions can now be seen to be equal. It is worth remembering
that these are not commutative monoids, and that thus the order of the
elements matters.

Lists are a suitable data structure for representing flat elements —
indices here — that can appear multiple times and whose order
carries meaning. In the case of commutative monoids, where order does
not carry meaning, a matrix of indices and the number of occurrences
of each could be represented as a vector of integers — where the
position in the vector represents the index and the content represents
the number of occurrences.

\ExecuteMetaData[Monoids.tex]{normal-form}

The normalising function ignores neutral elements and preserves order:

\ExecuteMetaData[Monoids.tex]{normalise}

From here on, I work with a concrete monoid (\AgdaBound{monoid}) on a
concrete carrier \AgdaBound{M}. This results in all of the definitions
inside of the module having \AgdaBound{M} and \AgdaBound{monoid}
defined. When called from the outside of this module, these
definitions have
\AgdaSymbol{\{}\AgdaBound{M}~\AgdaSymbol{:}~\AgdaPrimitiveType{Set}\AgdaSymbol{\}}~\AgdaSymbol{(}\AgdaBound{monoid}~\AgdaSymbol{:}~\AgdaRecord{Monoid}~\AgdaBound{M}\AgdaSymbol{)}
prepended to their type. I then make the insides of \AgdaBound{monoid}
directly accessible by opening it as if it were a module.

\begin{AgdaAlign}

\ExecuteMetaData[Monoids.tex]{monoid-module}

To evaluate an expression, a concrete assignment for the variables
contained within is needed. This is often called an environment. An
environment is a lookup table where each of the indices has an
associated value in the carrier \AgdaBound{M}.  The size of
\AgdaDatatype{Fin}~\AgdaBound{n} is equal to the size of
\AgdaDatatype{Vec}~\AgdaBound{M}~\AgdaBound{n}.

\ExecuteMetaData[Monoids.tex]{env}

Now that expressions, normal forms and environments are defined,
their evaluation can be defined too. Note that both definitions rule
out expressions and normal forms with more indices than the
environment contains — every index in the expression has to have a
corresponding value in the environment.

\ExecuteMetaData[Monoids.tex]{evaluation}

Bellow, the formal specification of soundness of the decision
procedure. If two monoids are decided equal, given any environment
they must evaluate to an equal value. However, no no claims can be
made if they are not decided equal: the carrier may have properties
other than the monoidal. (Take, for instance, the natural numbers with
addition, where $a + b$ is equivalent to $b + a$.)

\ExecuteMetaData[Monoids.tex]{solution}

The decidable equality of normal forms (here \AgdaFunction{\_≟\_}) is
defined as the decidable equality of lists that relies on the
decidable equality of finite indices.

\AgdaRef{Solution}~ is a specification defined for a given
equation. Such specification must be met for all equations:

\ExecuteMetaData[Monoids.tex]{solve-type}

If the evaluation of an expression can be shown to be decomposable
into its normalisation followed by the evaluation of such normal form,
then by congruence of functions, an equivalence of normal forms
implies an equivalence of terms after evaluation:

\phantomsection
\label{code:solve}
\ExecuteMetaData[Monoids.tex]{solve}

Put in a diagrammatic form, the following diagram must be shown to
commute:

\begin{figure}[h]
\centering
\begin{tikzpicture}[node distance=4cm,line width=1pt]
  \node (E)                             {\AgdaDatatype{Expr}~\AgdaBound{n}};
  \node (N)             [below of=E]    {\AgdaDatatype{NormalForm}~\AgdaBound{n}};
  \node (M)             [right of=N]    {\AgdaBound{M}};
  \draw[->] (E) to node [sloped, below] {\AgdaBound{l}~\AgdaSymbol{=}~\AgdaFunction{normalise}~\AgdaBound{e}} (N);
  \draw[->] (N) to node [sloped, below] {\AgdaFunction{⟦}~\AgdaBound{l}~\AgdaFunction{⇓⟧}~\AgdaBound{ρ}}      (M);
  \draw[->] (E) to node [sloped, above] {\AgdaFunction{⟦}~\AgdaBound{e}~\AgdaFunction{⟧}~\AgdaBound{ρ}}       (M);
\end{tikzpicture}
\caption{\AgdaSymbol{∀}~\AgdaBound{e}~\AgdaBound{ρ}~\AgdaSymbol{→}~\AgdaFunction{eval-commutes}~\AgdaBound{e}~\AgdaBound{ρ}}
\end{figure}

This proof is inductively defined and depends on another proof showing
that normalisation preserves a monoid's structure.

\ExecuteMetaData[Monoids.tex]{eval-commutes}

Unsurprisingly, together these two proofs use all of the monoid laws.

\ExecuteMetaData[Monoids.tex]{eval-homo}

\end{AgdaAlign}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Results and usage}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Proofs for arbitrary equations on monoids can automatically be
generated now:

\ExecuteMetaData[Monoids.tex]{eqn1-auto}

However, the user still needs to manually build the expressions
that represent the target theorem. This includes handling the indices
referring to variables appropriatly. As shown by \cite{Bove2009} at
\url{http://www.cse.chalmers.se/~ulfn/code/tphols09/}, index
referrences can be set up automatically, partially alleviating this
problem and resulting in the following usage:

\ExecuteMetaData[Monoids.tex]{eqn2-auto}

Agda's support for reflection can be used to build a macro that
inspects the type of the goal and translates it into a data structure
that the proof generating procedure can understand. This would result
in the following example usage:

\ExecuteMetaData[Monoids.tex]{eqn2-magic}

\todo{forward reference general verification}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Solving commutative rings}
\label{ch:rings}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

A commutative ring is a carrier set ~\AgdaBound{R}~ together with two
binary operations generalising multiplication and addition. Under
multiplication, ~\AgdaBound{R}~ is a commutative monoid; under
addition, an abelian group — providing an extra inverse law; and
multiplication distributes over addition.

\AgdaHide{
\begin{code}
module _ where
  open import Relation.Binary.PropositionalEquality
\end{code}}

\begin{code}
  record CommutativeRing (R : Set) : Set where
    infixl 5 _+_
    infixl 10 _*_
    infix 15 -_
    field
      _*_ : R → R → R
      1# : R
      *-assoc : (x y z : R) → (x * y) * z ≡ x * (y * z)
      *-comm : (x y : R) → x * y ≡ y * x
      *-identity : (x : R) → x * 1# ≡ x 

      _+_ : R → R → R
      0# : R
      +-assoc : (x y z : R) → (x + y) + z ≡ x + (y + z)
      +-comm : (x y : R) → x + y ≡ y + x
      +-identity : (x : R) → x + 0# ≡ x
      -_ : R → R
      +-inverse : (x : R) → x + - x ≡ 0#

      distrib : (x y z : R) → (y + z) * x ≡ (y * x) + (z * x)
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Problem description and specification}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\AgdaHide{
\begin{code}
  open import Data.Integer renaming (-_ to ℤ-_ ; _+_ to _ℤ+_ ; _*_ to _ℤ*_)
  open import Data.Integer.Properties as IntProp using ()
  INT-COMM-RING : CommutativeRing ℤ
  INT-COMM-RING = record
                    { _*_ = _ℤ*_
                    ; 1# = (+ 1)
                    ; *-assoc = IntProp.*-assoc
                    ; *-comm = IntProp.*-comm
                    ; *-identity = IntProp.*-identityʳ
                    ; _+_ = _ℤ+_
                    ; 0# = + 0
                    ; +-assoc = IntProp.+-assoc
                    ; +-comm = IntProp.+-comm
                    ; +-identity = IntProp.+-identityʳ
                    ; -_ = ℤ-_
                    ; +-inverse = IntProp.inverseʳ
                    ; distrib = IntProp.distribʳ
                    }
\end{code}}

Proving equalities on commutative rings can be tedious:

\begin{code}
  open CommutativeRing INT-COMM-RING
  eqn₃ : (x y z : ℤ) → y * (- ((+ 2) * x) + z + (+ 2) * x) ≡ y * z
  eqn₃ x y z = begin 
    y * ((- ((+ 2) * x) + z) + ((+ 2) * x))
      ≡⟨ cong (λ ● → y * (● + (+ 2) * x)) (+-comm (- ((+ 2) * x)) z) ⟩
    y * ((z + - ((+ 2) * x)) + ((+ 2) * x))
      ≡⟨ cong (λ ● → y * ●) (+-assoc z _ _) ⟩
    y * (z + (- ((+ 2) * x) + ((+ 2) * x)))
      ≡⟨ cong (λ ● → y * (z + ●)) (+-comm _ _) ⟩
    y * (z + ((+ 2) * x + - ((+ 2) * x)))
      ≡⟨ cong (λ ● → y * (z + ●)) (+-inverse ((+ 2) * x)) ⟩
    y * (z + (+ 0))
      ≡⟨ cong (y *_) (+-identity z) ⟩
    y * z
      ∎
    where open ≡-Reasoning
\end{code}

The goal of a problem solver for equalities on commutative rings is to
generate these proofs automatically for any commutative ring.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{A verified decision procedure}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Soon after I started to develop a solver in Agda, I found that Agda's
standard library already included one, and that it was far more
general than anything I could have written. I decided to comment on
their solution instead.

An automated solver for equations on commutative rings was provided in
\cite{Boutin1997} as an example use of reflection in automated theorem
proving. Coq's \texttt{ring} tactic implemented such solver. Later,
\cite{Gregoire2005} proposed a more performant solution, which Coq
adopted. \cite{Russinoff2017} adapts Grégoire and Mahboubi's solution
to the theorem prover ACL2 in a structured manner and is clarifying in
some regards.

Expressions are represented as polynomials that are indexed by the
number of variables in them. Shortcut functions for common operations
like addition, multiplication and subtraction are provided.

\ExecuteMetaData[CommutativeRings.tex]{expr}

The solver's high-level structure is similar to the monoid solver's
one described in \autoref{ch:monoids}. The heart of it proves that
evaluating a polynomial within an environment $ρ$ is equal to first
normalising it and then evaluating its normal form within $ρ$ — it
shows that normalisation is structure-preserving. Akin to
~\AgdaFunction{solve}~ in \autoref{code:solve}, this proof is then
used to conclude that if two normal forms are equivalent, so must the
original polynomials after evaluation be.

Polynomials with a single variable can be represented as
\textit{Horner normal forms}:

\begin{align*}
&a_{n} x^{n} + a_{n-1} x^{n-1} + \ldots + a_{0} \\
\equiv &((a_{n} x + a_{n-1}) x + \ldots) x + a_{0}
\end{align*}

\begin{AgdaAlign}
\ExecuteMetaData[CommutativeRings.tex]{hnf}

To make the solution multivariate, coefficients are replaced by
polynomials containing additional variables. Integer coefficients form
a commutative ring too, and thus this results in an opportunity to
handle both integer cofficients and coefficients containing additional
variables uniformly, as commutative rings.

\begin{align*}
&y^2 x^2 + y ^ 2 + y x + 2 x + 2 \\
\equiv &((0 + y y + 1) x + y + 2) x + y y + 2
\end{align*}

\ExecuteMetaData[CommutativeRings.tex]{normal}
\end{AgdaAlign}

In fact, the module does not require constant coefficients to be
integers. Any commutative ring that can be evaluated into the main
ring in a law-respecting manner and has decidable equality suffices.

\ExecuteMetaData[CommutativeRings.tex]{requirements}

The module handles equality generically, as a binary relation on the
carrier set. This and the need to evaluate constant coefficients
results in an inductive definition of equality of normal forms being
necessary.

Evaluation within an environment of both polynomial expressions and
normal forms is then defined. Similar to monoids, environments are
vectors of elements belonging to the carrier set, and need to be of
the same length as the number of unknowns in the polynomial or normal
form being evaluated. Evaluation of normal forms is then shown to be
congruent with repect to the inductive equality.

The exact choice of normal form influences both performance and the
complexity of proofs. The data type presented previously does not in
itself ensure the uniqueness of those normal forms that evaluate to $0$
— $0x$ can be represented both as ~\AgdaInductiveConstructor{∅}~ and
~\AgdaInductiveConstructor{∅}~\AgdaInductiveConstructor{*x+}~\AgdaInductiveConstructor{con}~\AgdaBound{C.0\#}.
To remedy this (and keep the size of terms small) a wrapper function
that (if pertinent) minimises univariate Horner normal forms to
~\AgdaInductiveConstructor{∅}~ is defined around
~\AgdaInductiveConstructor{\_*x+\_}.

Operations like addition and multiplication are defined for Horner
normal forms and then used by the normalisation process, which
operates inductively. Both the operations and the normalisation
process use the simplifying variant of
~\AgdaInductiveConstructor{\_*x+\_}~ to keep their results canonical.

For each operation, an homomorphism lemma is proven, showing that
evaluating the given operation on any two normal forms is equivalent
to evaluating both normal forms separately and then applying the given
operation to them. Finally, the main correctness proof uses these
lemmas to inductively proof that as a whole, normalisation respects
the structure of commutative rings.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Usage}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\AgdaHide{
\begin{code}
module _ where
  open import Data.Nat using (ℕ ; zero ; suc)
  open import Data.Integer
  import Data.Integer.Properties
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

  _^_ : ℤ → ℕ → ℤ
  x ^ zero = + 1
  x ^ (suc n) = x * (x ^ n)
  infixl 15 _^_
\end{code}}

An example usage of a ring solver for integers follows. The last
argument is an equality proof between the target theorem and the
theorem proven by the solver. This allows later rewrites and
adjustments.

\begin{code}
  open Data.Integer.Properties.RingSolver

  ex₁ : (x y z : ℤ)
      → x ^ 3 + y * x ^ 2 - x ^ 2 + + 2 * x * y + y ^ 2 - + 2 * x - + 2 * y
      ≡ (x + y - + 2) * (x ^ 2 + x + y)
  ex₁ = solve 3 (λ x y z → 
                   x :^ 3 :+ y :* x :^ 2 :- x :^ 2 :+ con (+ 2) :* x :* y
                   :+ y :^ 2 :- con (+ 2) :* x :- con (+ 2) :* y 
                := (x :+ y :- con (+ 2)) :* (x :^ 2 :+ x :+ y))
                refl
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Solving Presburger arithmetic}
\label{ch:presburger}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

In 1929, Mojżesz Presburger presented and proved decidable a predicate
logic on natural numbers (expandable to integers and real numbers)
with addition as its only operation. The original paper
\cite{Presburger1929} is in Polish and uses outdated notation;
\cite{Stansifer1984} contains an English translation and comments
clarifying the original. Several procedures capable of deciding
Presburger arithmetic exist, some of them I introduce later
on. Nevertheless, \cite{Fischer1974} showed that the worst case run
time of any such procedure is doubly exponential.

Here are some example simple predicates that better illustrate the
expressiveness of Presburger arithmetic.

\begin{align}
∀x.\:∃y.\:x=2y\,∨\,x=2y+1 \label{eq:even-or-odd} \\
∀x.\:¬∃y.\:2x=2y+1                               \\
∀x.\:4|x\,⇒\,2|x                                 \\
∀x.\:x\,<\,x + 1
\end{align}

To our knowledge, there is no other implementation of a decision
procedure for Presburger arithmetic written in Agda. In this chapter,
I introduce two decision procedures on integers, and partly implement
and verify correct one of them.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Problem description and specification}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

To solve Presburger arithmetic is to create a verified procedure
capable of deciding any well-formed Presburger predicate where all
variables are bound. Without an automated procedure, proving a
predicate like~\autoref{eq:even-or-odd} can already become burdensome:

\AgdaHide{
\begin{code}
module _ where
  private
    open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
    open import Data.Nat using (zero ; suc ; _*_ ; _+_)
    open import Data.Nat.Properties using (+-suc)
    open import Data.Product using (∃ ; _,_ )
    open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; cong ; sym)
\end{code}
}

\begin{code}
    pred₁ : ∀ n → ∃ λ m → ((n ≡ 2 * m) ⊎ (n ≡ 2 * m + 1))
    pred₁ zero = 0 , inj₁ refl
    pred₁ (suc zero) = 0 , inj₂ refl
    pred₁ (suc (suc n))                    with pred₁ n
    pred₁ (suc (suc .(m' + (m' + 0))))     | m' , inj₁ refl =
      suc m' , inj₁ (cong suc (sym (+-suc m' (m' + 0))))
    pred₁ (suc (suc .(m' + (m' + 0) + 1))) | m' , inj₂ refl =
      suc m' , inj₂ (cong suc (cong (_+ 1) (sym (+-suc m' (m' + 0)))))
\end{code}

I define Presburger predicates as any formulae built using the
following syntax:

\ExecuteMetaData[Presburger.tex]{formula}

I use de Bruijn indices \cite{Bruijn1972} to refer to bindings by
their proximity: a variable with index \AgdaNumber{0} refers to the
variable introduced by the most immediate binding to the left; index
\AgdaBound{n} refers to the variable introduced \AgdaBound{n} bindings
away. Using de Bruijn indices instead of variable names has two main
advantages:

\begin{itemize}[noitemsep]
  \item there is no need to rename variables on substitution; and
  \item the choice of variable names does not affect equality.
\end{itemize}

For any formula of type ~\AgdaDatatype{Formula}~\AgdaBound{n},
\AgdaBound{n} indicates the number variables introduced outside of that
formula. Quantifiers ~\AgdaInductiveConstructor{∀'\_}~ and
~\AgdaInductiveConstructor{∃'\_} make a new variable available to their
arguments.

\autoref{eq:even-or-odd} can be transcribed as follows:

\ExecuteMetaData[Presburger.tex]{pred}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Decision procedures}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

There exist numerous procedures capable of deciding Presburger
arithmetic. They are primarily distinguished by the domain of their
formulae and their requirements for normalisation. The satisfiability
of Presburger formulae in any domain gets carried onto superset
domains; the unsatisfiability onto subset domains, as noted in
\cite{Janicic1997a}.

\begin{figure}[h]
\centering
\begin{tikzpicture}[node distance=4cm,line width=1pt]
  \node (N)                             {ℕ};
  \node (Z)             [right of=N]    {ℤ};
  \node (Q)             [right of=Z]    {ℚ};
  \node (R)             [right of=Q]    {ℝ};
  \draw [->] (N.20)  -- (Z.160) node [pos=0.5,above] {$⊨_ℕ P \implies   ⊨_ℤ P$};
  \draw [<-] (N.340) -- (Z.200) node [pos=0.5,below] {$⊭_ℕ P \impliedby ⊭_ℤ P$};
  \draw [->] (Z.20)  -- (Q.160) node [pos=0.5,above] {$⊨_ℤ P \implies   ⊨_ℚ P$};
  \draw [<-] (Z.340) -- (Q.200) node [pos=0.5,below] {$⊭_ℤ P \impliedby ⊭_ℚ P$};
  \draw [->] (Q.20)  -- (R.160) node [pos=0.5,above] {$⊨_ℚ P \implies   ⊨_ℝ P$};
  \draw [<-] (Q.340) -- (R.200) node [pos=0.5,below] {$⊭_ℚ P \impliedby ⊭_ℝ P$};
\end{tikzpicture}
\caption{Decidability across domains}
\end{figure}

Some Presburger formulae are valid on integers but invalid on natural
numbers: $∃x.\:x+1=0$. Others are valid on rational numbers but
invalid on integers: $∃x.\:2x=1$. When considering which decision
procedures to explore, I immediately discarted the ones acting on real
numbers — irrational numbers are not straightforward to handle in
constructive mathematics. The most well-documented procedures are on
integers, and the usage of integer Presburger arithmetic is common
enough for an automated solver to be of great value. Given a solver
for problems on integers, one just needs add the condition $0 \leq x$
to every existential quantifier to solve problems on natural numbers.

I chose the Omega Test and Cooper's Algorithm as the two integer
decision procedures to explore. Michael Norrish depicts in
\cite{Norrish2003} the state of affairs concerning the implementation
of Presburger arithmetic deciding procedures by proof assistants. He
then continues describing the Omega Test and Cooper's Algorithm and
proposes verified implementations for both of them for the proof
assistant HOL. A later talk gives additional details.
\cite{Norrish2006}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{The Omega Test}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

The Omega Test was first introduced in \cite{Pugh1991}. It adapts
Fourier-Motzkin elimination — which acts on real numbers — to
integers, and requires the input formula to be put in disjunctive
normal form.

This section starts by implementing a normalisation procedure that
puts input formulae into their equivalent normal forms. It then takes
a leap and implements variable elimination for quantifier-free
existential formulae and verifies it sound. Finally, it provides the
reader with some usage examples and outlines future work.

This section is significantly based on the material found in
\cite{Norrish2003} and \cite{Norrish2006}.

\subsection{Normalisation}
\label{sec:normalisation}

Transforming input formulae into disjunctive normal forms can blow up
the size of formulae exponentialy, as can clearly be seen whenever a
conjunction is normalised over a disjunction:

\begin{equation*}
(P \lor Q) \land (R \lor S) \equiv (P \land R) \lor (P \land S) \lor
(Q \land R) \lor (Q \land S)
\end{equation*}

As part of normalisation, universal quantifiers need to be transformed
into existential ones resorting on the following equivalence:

\begin{equation*}
∀x.P(x) \equiv ¬∃x.¬P(x)
\end{equation*}

Existential quantifiers must be distributed over disjunctions:

\begin{equation*}
∃x.\:P(x) \lor Q(x) \equiv (∃x.\:P(x)) \lor (∃x.\:Q(x))
\end{equation*}

Negation needs to be pushed inside conjunctions and disjunctions, and
double negation needs to be eliminated:

\begin{align*}
\neg (P(x) \land Q(x)) &\equiv \neg P(x) \lor  \neg Q(x) \\
\neg (P(x) \lor  Q(x)) &\equiv \neg P(x) \land \neg Q(x) \\
\neg \neg P(x)         &\equiv P(x) 
\end{align*}

Operations on ~\AgdaDatatype{Atom}s are evaluated into linear
transformations of the form $ax + by + \ldots + cz + k$. As a
consequence of limiting the domain to the integers, all constraints
are translated into a canonical form $0 \leq ax + by + \ldots + cz +
k$. I use a single type to represent them both, and a parameter on
that type to keep record of the number of variables within. A vector
of that same length contains the coefficients $ax + by + \ldots + cz$,
where each coefficient's index is a de Bruijn index indicating the
distance in bindings to where that variable was introduced. An
additional constant is used to represent $k$.

\ExecuteMetaData[Presburger.tex]{linear}

Relations are normalised as follows:

\begin{align*}
p < q    &\equiv 0 \leq q - p + 1 \\
p > q    &\equiv 0 \leq p - q + 1 \\
p \leq q &\equiv 0 \leq q - p     \\
p \geq q &\equiv 0 \leq p - q     \\
p = q    &\equiv 0 \leq q - p \land 0 \leq p - q
\end{align*}
  
Divide terms and their negations are special cases. The Omega Test
produces them as a byproduct of its main theorem and uses a specific
algorithm to eliminate them, as shown later. However, I do not
implement such a procedure (discussed later) so I normalise divide
terms into constraints by introducing a new existential quantifier:

\begin{align*}
n ∣ a &\equiv ∃x.\:nx = a \\
n ∤ a &\equiv ∃x.\:\bigvee_{i ∈ 1 \ldots n - 1} nx = (a + i)
\end{align*}

Taking all into account, the result of normalisation has to be a
structure where:

\begin{enumerate*}[label=(\roman*)]
  \item the top layer is a disjunction;
  \item a disjunction only contains conjunctions; and
  \item a conjunction only contains conjunctions, existential
        quantifiers, negated existential quantifiers, or atoms.
\end{enumerate*}

The following tree-like structure contains ~\AgdaDatatype{Linear}s as
leafs and, within each conjunction, distinguishes leafs from further
subtrees containing existential quantifiers.

As with ~\AgdaDatatype{Formula}s, note that the restriction on the
number of available variables is pushed inside the structure —
~\AgdaDatatype{DNF}~\AgdaBound{n} can only contain
~\AgdaDatatype{Conjunction}~\AgdaBound{n}~ and so forth. The
constructors ~\AgdaInductiveConstructor{∃}~ and
~\AgdaInductiveConstructor{¬∃}~ make one more variable available to
their substructures.

\ExecuteMetaData[Presburger.tex]{normal-form}

Normalisation proceeds recursively, eliminating universal quantifiers,
pushing conjunction and negation inward, normalising implication,
evaluating operations on atoms and normalising relations between
them. For the exact procedure see the accompainying code.

\subsection{Elimination}

Once normalisation has taken place, the elimination process is ran
recursively on quantifier-free sub-formulae. The heart of this is an
equivalence theorem that eliminates the variable bound by the
innermost existential quantifier:

\begin{equation*}
∃x.P(x) \equiv Q
\end{equation*}

\begin{theorem}[Pugh, 1991]
Let $L(x)$ be a conjunction of lower bounds on $x$, indexed by $i$, of
the form $a_i \leq \alpha_i x$, with $\alpha_i$ positive and
non-zero. Similarly, let $U(x)$ be a set of upper bounds on $x$,
indexed by $j$, of the form $\beta_j x \leq b_j$, with $\beta_j$
positive and non-zero. Let $m$ be the maximum of all $\beta_j$s. Then:

\begin{align*}
(∃x.L(x) ∧ U(x)) &\equiv
\left(\bigwedge_{i,j} (\alpha_i - 1)(\beta_j - 1) \leq (\alpha_i b_j - a_i \beta_j)\right) \\
&\qquad {} \qquad {} \qquad {} \qquad {} \qquad {} \lor \\
&\qquad {} \bigvee_i \bigvee^{\left\lfloor \alpha_i - \frac{\alpha_i}{m} - 1 \right\rfloor}_{k=0}
∃x. (\alpha_i x = a_i + k) \land L(x) \land U(x)
\end{align*}
\end{theorem}

Pugh refers to the first disjunct as the \textit{real shadow} and to
the remaining as \textit{splinters}. If all $\alpha_i$ or all
$\beta_j$ are $1$ — that is, if for every $(\alpha , \beta)$ pair
$\alpha \equiv 1 \lor \beta \equiv 1$ —, the theorem reduces to the
\textit{exact shadow}:

\begin{align*}
∃x.L(x) ∧ U(x) \equiv \bigvee_{i,j} a_i \beta_j \leq \alpha_i b_j
\end{align*}

My initial intention was to implement and verify the complete
theorem. However, I quickly found out about the complexity introduced
by splinters. Each splinter introduces a new existential
quantifier. This quantifier is then eliminated by the following
terminating method based on the Euclidean algorithm for the
computation of greatest common divisors:

\begin{align}
  \shortintertext{$x$ is the variable to eliminate}
  ∃y. ∃x. &\ldots \land ax = by + e \land \ldots \\
  \shortintertext{Find the lowest common divisor $ℓ$ of all the
        coefficients on $x$ and multiply every constraint by an
        integer $n$ so that its coeffiecient on $x$ is $ℓ$}
  ∃y. ∃x. &\ldots \land ℓx = b'y + e' \land \ldots \\
  \shortintertext{Set all coeffients on $x$ to $1$ resorting to the
        equivalence $P(ℓx) \equiv P(x) \land ℓ ∣ x$.}
  ∃y. ∃x. &\ldots \land (x = b'y + e') \land (ℓ ∣ x) \land \ldots \\
  \shortintertext{Substitute $x$}
  ∃y. &\ldots \land ℓ ∣ b'y + e' \land \ldots \label{eq:divides} \\
  \shortintertext{Eliminate the divides term by introducing a new existential}
  ∃y. ∃z. &\ldots \land ℓz = b'y + e' \land \ldots \\
  \shortintertext{Rearrange}
  ∃y. ∃z. &\ldots \land b'y = ℓz - e' \land \ldots
  \shortintertext{$y$ is the variable to eliminate} \nonumber
\end{align}

Crucially, \autoref{eq:divides} guarantees the eventual elimination of
the divides term, as $b' < ℓ$ — and modulus if not. This recursive
computation, justified because a transitive relation towards the left
on $<$ for natural numbers eventually terminates, is not entirely
trivial to model. Commonly, structural recursion is applied onto terms
that have been deconstructed by pattern matching — and thus structures
get smaller in ``fixed steps''. Here, on the other hand, recursion has
to be shown to terminate by account of the divides term's coefficient
decreasing in steps of variable size.

\todo{NatRec}

As for verification, splinters introduce considerable complexity too.
Pugh's theorem is of form $\text{LHS} \equiv D_1 \lor D_2$. That
shapes the proof, which first shows the soundness of both disjuncts by
proving that $D_1 \implies LHS$ and $D_2 \implies \text{LHS}$ and then
its completeness by proving that $\text{LHS} \land \neg D_1 \implies
D_2$. From these three proof obligations, the last one is the hardest
to satisfy.

After some initial exploratory programming, given the complexity
they entail, both in terms of implementation and verification, and
taking time constraints into account, I decided to discard
implementing splinters. Other interactive theorem provers like Coq,
HOL or Isabelle, limit the completeness of their implementations too,
often just to the real shadow.

This decision left me with two components:

\begin{description}

  \item [Dark shadow] Always applicable. Formulae decided satisfiable
  after elimination can be shown to be satisfiable before elimination.

  \item [Real shadow] Only applicable when all $\alpha$ or all $\beta$
  are $1$. It preserves both satisfiability and unsatisfiability.

\end{description}
  
A decision procedure with only these tests is sound but incomplete,
and thus has three possible outcomes:

\ExecuteMetaData[Presburger.tex]{result}

Implementing the dark shadow is not involved. With $l$ as the lower
bound constraint, $u$ as the upper bound and $\alpha$, $a$, $\beta$
and $b$ as per Pugh:

\ExecuteMetaData[Presburger.tex]{dark-shadow}

The dark shadow reduces to the real shadow when all $\alpha_i$ or all
$\beta_j$ are $1$. I use the function ~\AgdaFunction{dark-shadow}~ for
both computations, and then interpret the results accordingly.
Unsatisfiability can only be asserted if the real shadow's
precondition is met. If it is not,
~\AgdaInductiveConstructor{unsatisfiable}~ needs to be interpreted as
~\AgdaInductiveConstructor{undecided}. Following, an elimination
procedure for quantifier free formulae.
~\AgdaFunction{⊨?\_[}~\AgdaInductiveConstructor{[]}~\AgdaFunction{/x]}~
decides constraints with no variables, as shown in the next section.

\ExecuteMetaData[Presburger.tex]{elimination}

\subsection{Verification}

This subsection verifies the soundness of the incomplete elimination
procedure on quantifier-free formulae presented above. The exact
specification follows:

\ExecuteMetaData[Presburger.tex]{correctness}

No proof is required if the procedure is incapable of deciding the
input; an environment satisfying the input is required if the input is
decided satisfiable; a function showing the inadequacy of any given
environment is required if the input is decided unsatisfiable. The
goal is to satisfy this predicate for any conjunction of constraints.
(The meaning of ~\AgdaFunction{⊨}~ is explained below.)

\subsubsection{Preamble}

Although their definitions are available in the source code
accompanying this report, my aim is to provide the reader with an
intuition of the meaning of some of the different symbols used in this
subsection.

\begin{description}
  \item [\AgdaFunction{Env}~\AgdaBound{i}]
  An environment with ~\AgdaBound{i}~ variables, usually named
  ~\AgdaBound{ρ}.

  \item [\AgdaFunction{LowerBound},~\AgdaFunction{Irrelevant},~\AgdaFunction{UpperBound}]
  Predicates on a linear's innermost variable's coefficient $c$. They
  state $0<c$, $0=c$ and $0>c$ respectively.

  \item [\AgdaFunction{Pair}~\AgdaBound{i}]
  A pair of lower bound and upper bound constraints, usually named
  ~\AgdaBound{lu}.
  \ExecuteMetaData[Presburger.tex]{pair}

  \item [\AgdaFunction{[}~\AgdaBound{ρ}~\AgdaFunction{/x]}~\AgdaBound{a}]
  The integer result of substituting the variables in ~\AgdaBound{a}~
  with the values in the environment ~\AgdaBound{ρ} and evaluating.

  \item [\AgdaFunction{⊨[}~\AgdaBound{ρ}~\AgdaFunction{/x]}~\AgdaBound{a}]
  The foundation stone of verification: the interpretation of the
  value ~\AgdaBound{a}~ as a type after substitution.

  \ExecuteMetaData[Presburger.tex]{meaning}

  \item [\AgdaFunction{⊨?}~\AgdaBound{a}~\AgdaFunction{[}~\AgdaBound{ρ}~\AgdaFunction{/x]}]
  A function deciding whether the interpretation of ~\AgdaBound{a}
  after substitution is inhabited.

  \item [\AgdaFunction{⊨}~\AgdaBound{as}]
  An environment satisfying every ~\AgdaBound{a}~ in ~\AgdaBound{as}~
  after substitution.
  \ExecuteMetaData[Presburger.tex]{meaning-all}
  
  \item [\textnormal{Variations} \AgdaSymbol{…}\AgdaFunction{ₚ}]
  For convenience. The function is applied to a pair of lower bound
  and upper bound constraints.

  \item [\textnormal{Variations} \AgdaSymbol{…}\AgdaFunction{ᵢ}]
  For convenience. The function is applied to an irrelevant
  constraint.

  \item [\AgdaFunction{∀[}~\AgdaBound{xs}~\AgdaFunction{]}~\AgdaBound{P}]
  The proof that ~\AgdaBound{P}~\AgdaBound{x}~ for every ~\AgdaBound{x}~
  in ~\AgdaBound{xs}.

  \item [\AgdaFunction{∃[}~\AgdaBound{xs}~\AgdaFunction{]}~\AgdaBound{P}]
  The proof that ~\AgdaBound{P}~\AgdaBound{x}~ for some
  ~\AgdaBound{x}~ in ~\AgdaBound{xs}.
\end{description}

\subsubsection{Dark shadow}

The goal is to prove that the elimination performed by the dark shadow
preserves satisfiability: whenever a formula is satisfiable after
applying dark shadow elimination to it, it must be shown to be
satisfiable before elimination too.

\begin{equation*}
\bigwedge_{i,j} (\alpha_i - 1)(\beta_i - 1) \leq \alpha_i b_j - a_i \beta_j
\implies ∃x. L(x) \land U(x)
\end{equation*}

The original proof proceeds by induction on every $L(x) × U(x)$ pair,
where the proof obligation is fulfilled resorting to a proof by
contradiction:

\begin{equation*}
\neg (∃x. a \leq αx \land βx \leq b) \implies
\neg (\alpha - 1)(\beta - 1) \leq \alpha b - a \beta
\end{equation*}

However, $P$ cannot be generally concluded from $¬P → ⊥$ in
constructive mathematics: the first requires a witness $p : P$ that
the later does not provide. Nevertheless, a proof by contradiction
still has its use. If the elements to test for $P$ can be limited to a
finite set, a proof by contradiction — showing that it cannot be that
$P$ is false for every element — can be used to build a terminating
search function that is guaranteed to find an element satisfying $P$.

Below I present such a generalised search function, searching within a
finate list for elements satisfying a decidable predicate.

\ExecuteMetaData[Presburger.tex]{search}

In this case, the search is for some $x$ that satisfies a conjunction
of constraints of form $a \leq \alpha x \land \beta x \leq b$, with
$\alpha$ and $\beta$ positive and non-zero. For every constraint, $x$
must be bound between $\left\lfloor\frac{a}{α}\right\rfloor$ and
$\left\lceil\frac{b}{β}\right\rceil$; the conjunction of all
constraints must be bound between such highest lower bound and such
lowest upper bound.

\ExecuteMetaData[Presburger.tex]{search-space}

The proof outlined by Norrish is be used as a guarantee for the
success of the search. However, while Norrish's proof by contradiction
is on individual constraint pairs\ldots

\ExecuteMetaData[Presburger.tex]{norrish-type}

\ldots the search function demands a proof by contradiction on the
entire conjunction of constraint pairs.

\ExecuteMetaData[Presburger.tex]{by-contradiction-type}

Nevertheless, the premise that must be proven false (informally,
$∀x.¬∀lu.⊨ₓlu$) is equivalent to the form $∃lu.¬∃x.⊨ₓlu$ — where every
$l$ is paired with every $u$. This later form is suitable to be fed
into Norrish's proof by contradiction, which for any $lu$ expects
$¬∃x.⊨ₓlu$. The difference is that Norrish's proof is used only
once. Note that the unsolved postulate is the same justification
required by Norrish's initial induction. The proof is a one-way
implication, but bi-implication can be shown.

\ExecuteMetaData[Presburger.tex]{contradiction-adaptation}

Finally, the $lu$ pair for which $¬∃x.⊨ₓlu$ must be found,
Norrish's proof executed on it and
~\AgdaBound{⊨Ωlu}~\AgdaSymbol{→}~\AgdaDatatype{⊥}~ derived and applied
to ~\AgdaBound{⊨Ωlu}.

\ExecuteMetaData[Presburger.tex]{contradiction-search}

Put together, this satisfies the proof by contradiction:

\ExecuteMetaData[Presburger.tex]{by-contradiction-type}
\ExecuteMetaData[Presburger.tex]{by-contradiction}

The proof by contradiction can then be used to guarantee the success
of the search for $x$: 

\ExecuteMetaData[Presburger.tex]{find-x}

\subsubsection{Norrish's proof}

Below, I briefly reproduce Norrish's proof of soundness for the dark
shadow. For every pair of lower bound and upper bound constraints, it
has to be shown that:

\begin{equation*}
(\alpha - 1)(\beta - 1) \leq \alpha b - a \beta \implies
(∃x. a \leq αx \land βx \leq b)
\end{equation*}

To prove it, assume the opposite. Then, there is no multiple of
$\alpha \beta$ between $a \beta$ and $\alpha b$:

\begin{equation*}
\neg ∃x. a \beta \leq \alpha \beta x \leq \alpha b
\end{equation*}

As both $0 < \alpha$ and $0 < \beta$, the other assumption implies
that $a \beta \leq \alpha b$. Take $i$ to be the greatest multiple of
$\alpha \beta$ less than $a \beta$. Then

\begin{equation*}
\alpha \beta i < a \beta \leq \alpha b < \alpha \beta (i + 1)
\end{equation*}

Because $0 < \alpha \beta (i + 1) - \alpha b$, conclude $1 \leq \beta
(i + 1)$, and thus $\alpha \leq \alpha \beta (i + 1) - \alpha
b$. Similarly, $\beta \leq a \beta - \alpha \beta i$. Infer $\alpha +
\beta \leq \alpha \beta + a \beta - \alpha b$, or (re-arranging),
$\alpha b - a \beta < \alpha \beta - \alpha - \beta + 1$, which
contradicts the first assumption.

I do not intend to reproduce here the entire proof as written in
Agda. In fact, time constraints and the low priority I assigned to
filling in the details made me keep some sub-goals as unfinished
postulates. Instead, I show how the main goal is split into smaller
sub-goals and how those are later put back together. I also give an
example of a finished sub-goal proof to show the reader what it looks
like.

I use a parametrised module for every proof that involves a particular
lower bound and upper bound pair. I \textit{open} the constituents of
the supplied pair so that I can refer to them more comfortably from
within types.

\begin{AgdaAlign}

\ExecuteMetaData[Presburger.tex]{norrish-inner-header}

I define the form of some sub-goals separately, so that I can later
refer to them from within multiple types too.

\ExecuteMetaData[Presburger.tex]{goal-example}

Next, a proof for one of the sub-goals, where I show that $(\alpha -
1)(\beta - 1) \leq \alpha b - a \beta$ implies $a \beta \leq \alpha b$
when both $0 < \alpha$ and $0 < \beta$. Observations that are a common
requirement to multiple sub-goals have been abstracted away into
lemmas.

\ExecuteMetaData[Presburger.tex]{example-subgoal}
\end{AgdaAlign}

Putting the remaining sub-goals together, I supply Norrish's proof:

\ExecuteMetaData[Presburger.tex]{norrish-type}
\ExecuteMetaData[Presburger.tex]{norrish}

\subsubsection{Real shadow}

The dark shadow preserves satisfiability. It must be shown that
whenever the real shadow is applied, unsatisfiability is preserved
too. Where all $\alpha_i$ or all $\beta_i$ are $1$:

\begin{equation*}
\neg \bigwedge_{i,j} (\alpha_i - 1)(\beta_j - 1) \leq \alpha_i b_j - a \beta_j
\implies \neg ∃x. L(x) \land U(x)
\end{equation*}

That is, given arguments $\bigwedge_{i,j} (\alpha_i - 1)(\beta_j - 1)
\leq \alpha_i b_j - a \beta_j \implies \bot$ and $∃x. L(x) \land U(x)$,
the latter must be transformed into an argument suitable for the
former. Using induction, the proof obligation can be reduced to a
predicate on lower bound and upper bound pairs.

\begin{equation*}
(∃x. a \leq \alpha x \land \beta x \leq b)
\implies (\alpha - 1)(\beta - 1) \leq \alpha b - a \beta
\end{equation*}

The conjuncts on the LHS of the implication are appropriately
multiplied, then $a \beta \leq \alpha b$ by transitivity of
$\leq$. The proof concludes as $(\alpha - 1)(\beta - 1)$ reduces to
$0$ when either $\alpha$ or $\beta$ are $1$. Below, such a proof
written in Agda.

\ExecuteMetaData[Presburger.tex]{real-shadow}

\subsubsection{Delivering soundness}
\label{sec:soundness}

Next, I prove the soundness of the elimination procedure for
normalised formulae of the following form:

\begin{equation*}
∃x. ∃x_1 . \ldots ∃x_n . \; 0 \leq A[x, x_1 , \ldots , x_n] \land 0 \leq B[x, x_1, \ldots , x_n] 
\end{equation*}

The elimination process has to be shown to preserve both
unsatisfiability and satisfiability. I do not reproduce these proofs
here, they are rather bulky. Instead, I comment on their logic,
although I recommend reading their code alongside.

\ExecuteMetaData[Presburger.tex]{correct}

Both proofs are recursively built. If an input is decided
unsatisfiable (goal ~\AgdaBound{⊨as→⊥}), a proof of unsatisfiability
after elimination (\AgdaBound{⊨as↓→⊥}) is obtained recursively. Then
satisfiability before elimination is assumed (\AgdaBound{⊨as}) and
satisfiability after elimination derived (\AgdaBound{⊨as↓}) through
the use of ~\AgdaFunction{⊨real-shadow}.= From there, a contradiction
is obtained.

If an input is decided satisfiable (goal ~\AgdaBound{⊨as}), a proof of
satisfiability after elimination (\AgdaBound{⊨as↓}) is obtained
recursively. Then ~\AgdaFunction{find-x}~ adds a new $x$ to the
environment, and returns a proof (\AgdaBound{⊨as}) that by doing so,
satisfiability is preserved.

Clearly, irrelevant constraints — those where the variable to
eliminate has coefficient 0 — do not have their meaning altered after
elimination. Similarly, the meaning of no constraint changes after an
irrelevant variable is prepended to it. Given that the Omega Test
requires constraints to be split into lower bounds and upper bounds, I
handle irrelevant constraints outside of the it.

\AgdaFunction{partition}~ partitions a list of constraints into three
sub-lists: lower bound constraints, irrelevant constraints and upper
bound constraints. Functions ~\AgdaFunction{pairs}~ and
~\AgdaFunction{irrels}~ then use such output to generate a cartesian
product of all lower bound and upper bound constraints, and a list of
irrelevant constraints, respectively.  These functions carefully avoid
pattern matching on the output of ~\AgdaFunction{partition}. If they
were to pattern match, Agda would no longer relate the results of
~\AgdaFunction{pairs}~ and ~\AgdaFunction{irrels}~ to the original
list.

The function ~\AgdaFunction{entangle}~ mixes together proofs on pairs
of bounds and proofs on irrelevant constraints into proofs on their
original list. ~\AgdaFunction{untangleⁱ}~ and
~\AgdaFunction{untangleᵖ}~ do the reverse. If the satisfiability
predicate were to be defined on sets instead of on lists, these
functions would become unncesessary.

\todo{Some kind of diagram?}

\subsection{Results and usage}
\label{sec:usage}

To demonstrate an example usage of the presented elimination
procedure, I slightly augment the syntax of the normalised input
formulae handled by the soundness proof and include negated
existentials.

\ExecuteMetaData[Adaptation.tex]{normal-form}

Accepting universal quantifiers implies accepting full-blown
normalised Presburger formulae (because $∀x.P(x) \equiv ¬∃x.¬P(x)$,
which results in disjunctions if $P(x)$ contains conjunctions).
Accepting full-blown normalised Presburger formulae as presented in
\autoref{sec:normalisation} increases the complexity of the proof of
soundness. I restrict the syntax of unnormalised expressions
accordingly and mark the handling of full-blown Presburger formulae
for future work.

The elimination procedure negates its output and ultimately relies on
the previouly defined ~\AgdaFunction{Ω}.

\ExecuteMetaData[Adaptation.tex]{elimination}

Soundness is defined for such elimination procedure and proven in a
way similar to the proof in \autoref{sec:soundness}. This time, the two
functions proving satisfiability and unsatisfiability recurse on each
other every time an existential quantifier is negated.

Following, a set of example usages. The terms inside of
\texttt{\{!…!\}} are not accepted by the type-checker:

\ExecuteMetaData[Adaptation.tex]{examples}

\subsection{Future work}
\label{sec:future-work}

Although the present development is in my view satisfactory, there is
ample room for further work. Below is a to-do list, ordered by
priority, of what my work after submission is likely to be.

\begin{description}

  \item [Removal of postulates] Currently several base lemmas remain
  postulates and so do several lemmas used by Norrish. Fulfilling
  these is a priority and — I am confident — a very realistic
  goal. Once completed, Agda can compile the program in safe mode:
  after that the correctness of the program is proven beyond any
  reasonable doubt.

  \item [Evaluation of normal forms] Evaluation is currently defined
  for a subset of input formulae.  Evaluating full-blown formulae
  requires managing more complex forms of environments. Still, these
  more complex environments would only need to be handled by the
  ``outer'' layer of the soundness proof; the implementation of
  Norrish's proof would not need to be changed.

  \item [Verification of the normalisation process] Because I had not
  enough time to evaluate normal forms, I did not attempt to verify
  normalisation correct either. Although fairly labourious, I do not
  expect this to be too challenging.

  \item [Quoting] Building input formulae automatically out of users'
  goals is a major usability improvement.

  \item [Submission to the standard library] Submitting my
  development for inclusion in Agda's standard library would be the
  culmination of this work. There is no guarantee this will happen
  and, if it does, I expect it to entail considerable communication
  and adaptation work.
  
  \item [Implementation and verification of splinters] Most proof
  assistants provide incomplete Presburger solvers that do not make
  use of splinters. Given the complexity of implementing and verifying
  them, this as an entirely optional goal.
  
\end{description}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Cooper's Algorithm}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

During my initial research phase, I briefly considered Cooper's
Algorithm as a candidate for a verified Presburger arithmetic
solver. First introduced in \cite{Cooper1972}, \cite{Norrish2003} and
\cite{Chaieb2003} provide comprehensible reviews and discuss
implementation details.

The main elimination theorem handles both disjunctions and
conjunctions, and thus there is no need to normalise input formulae
into DNF or CNF, but negation needs to be pushed inside. Once a
quantifier-free expression is selected for variable elimination, the
lowest common multiplier $ℓ$ of all coefficients on $x$ needs to be
computed, all constraints multiplied appropriately so that their
coefficients on $x$ are $\pm ℓ$ and finally, all coefficients on $x$
divided by $ℓ$ in accordance to the following equivalence:

\begin{equation*}
P(ℓx) \equiv P(x) \land ℓ | x
\end{equation*}

Implementing the main elimination step is straightforward as well. The
main theorem operates on divides terms too, and there is therefore no
need to eliminate them.

As with the Omega Test, elimination occurs into an equivalent
disjunction, which leaves three goals to be verified — $D_1 \implies
LHS$, $D_2 \implies \text{LHS}$ and $\text{LHS} \land \neg D_2
\implies D_1$. However, unlike with the Omega Test, no shortcut can be
applied to decide a formula unsatisfiable, partly verifying the
theorem results in an incomplete procedure only capable of announcing
the satisfiability of a formula. Verifying the whole theorem is
considerably more complex than verifying the totality of the Omega
Test, and I therefore discarted the more efficient Cooper's Algorithm
in favour of the simpler Omega Test.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Verification and validation}
\label{ch:verification}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Dependent types facilitate definitions up to a great level of
precision. These types are used to accurately model specifications. A
formal specification is then considered to have been met if a term
inhabiting its corresponding type is supplied. No amount of anecdotal
evidence (testing) can attain the grade of verification attained by
these machine-checked formal proofs.

\todo{refer to the exact sections}

For the exact details on the verification of the software developed
for this report, I refer the reader to the corresponding sections in
\autoref{ch:monoids}, \autoref{ch:rings} and \autoref{ch:presburger}
and to the accompanying source code. The brevity of this chapter is a
consequence of the central role that verification plays through the
entire work.

Due to time contraints, some propositions in \autoref{ch:presburger}
remain postulates and therefore circumvent all verification. However,
these are all relatively simple lemmas or have been proven correct in
\cite{Norrish2003}, and I am confident that with sufficient time I
could satisfy them. If these postulates are accepted as truthful, the
rest of the developed software follows as verified.

This report and the accompanying source code are literate Agda
files. They must be type-checked to automaticly highlight their
syntax. This occurs as part of the build process every time this
report is built.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Overall evaluation}
\label{ch:evaluation}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This project set out to research the construction of evidence
providing problem solvers in Agda. I selected three problems to
explore: equations on monoids, for which I provide a completely
verified solver; equations on commutative rings, for which I gained
insight from an already existing solution; and Presburger arithmetic,
for which I build a solution for the first time implemented in Agda.

The solutions in \autoref{ch:monoids} and \autoref{ch:rings} are final
— they fully settle their respective problems. The solution for
\autoref{ch:presburger} is not, hence I outline future work in
\autoref{sec:future-work}. Nevertheless, in \autoref{sec:usage} I
provide a limited interface through which the user can benefit from my
work.

There exists no reasonable doubt about the correctness of the solver
for monoids, the solver for commutative rings or, obviating
postulates, the solver for Presburger arithmetic. The postulated
claims are all reasonable to make and have, in many cases, already
been proven by others.

The research work involved in this project has been considerable —
particularly during the problem selection phase. Although two
deliverables were produced, this project was primarily a research
project. A plethora of little discoveries had to be made and often,
progress was slow and irregular. As my supervisor well put it, my
learning process was by implosion: I started with a multitude of
ill-defined concepts and vague ideas and no sense of their
relevance. They were gradually refined and made more precise.

In the course of this project, and sometimes indirectly, I learned
bits and pieces about abstract algebra, type theory, category theory
and logic. I now better understand what it is to solve a problem
constructively; how proofs of correctness are structured; how Agda's
pattern matching and unification works; and what dependent types have
to bring to the table. Finally, the experience of interpreting and
formally reproducing a scientific paper has been invaluable.

\section{Organisation}

I used my blog mostly to sketch new ideas and take notes, not so much
for planning. For that, I relied on my whiteboard — the source of all
organisation in my living. Once I started writing this report, I used
the \LaTeX package \texttt{todonotes} to keep track of tasks within
the report itself. Tasks are highlighted as big orange notes on the
sides of pages, and are impossible to miss during reviews. I used
\texttt{grep} to list all these tasks.

Bellow is a brief timeline for this project:

\newpage
\begin{multicols}{2}
\begin{description}[style=unboxed,leftmargin=0cm]
  \item [2017-10] \hfill \\
    \vspace{-\topsep}
    \begin{itemize}
      \item understand what an evidence providing problem solver is
      \item start absorbing the literature
      \item start blog
    \end{itemize}
  \item [2017-11] \hfill \\
    \vspace{-\topsep}
    \begin{itemize}
      \item solve equations on monoids
      \item start reading about solving equations on commutative rings
    \end{itemize}
  \item [2017-12] \hfill \\
    \vspace{-\topsep}
    \begin{itemize}
      \item examine the existing solution for commutative rings
      \item start reading about solving Presburger arithmetic
    \end{itemize}
  \columnbreak
  \item [2018-01] \hfill \\
    \vspace{-\topsep}
    \begin{itemize}
      \item start working on solving Presburger arithmetic
    \end{itemize}
  \item [2018-02] \hfill \\
    \vspace{-\topsep}
    \begin{itemize}
      \item decide what decision algorithm to use for Presburger arithmetic
      \item write the background chapter
      \item polish the monoid solver
      \item write the chapter on solving monoids
    \end{itemize}
  \item [2018-03] \hfill \\
    \vspace{-\topsep}
    \begin{itemize}
      \item solve Presburger arithmetic
      \item write the chapter on solving Presburger arithmetic
      \item write the chapter on solving commutative rings
    \end{itemize}
\end{description}
\end{multicols}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Summary and conclusions}
\label{ch:conclusion}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

This report researches the construction of verified problem solvers
for three distinct problem domains. \autoref{ch:monoids} provides a
detailed description of a solver for equations on monoids;
\autoref{ch:rings} examines an existing solution for equations on
commutative rings and draws parallelisms to the solution for monoids;
\autoref{ch:presburger} is an ongoing attempt to define a solver for
Presburger arithmetic in Agda.

Time constraints limited my work on the Presburger arithmetic solver.
Much is still to be done, but the contributed work encompasses the
heart of it — and provides an interface for a subset of Presburger
formulae to be proven. Future work is outlined in
\autoref{sec:future-work}.

Perhaps most importantly, this project has been of invaluable
educational significance. I will likely aspire to find further
entertainment within the field.

\bibliographystyle{apalike}
\bibliography{bibliography}

\begin{appendices}

\chapter{Program listing}

The sources necessary to build this report — including the source
files that contain all the quoted code listings — can be found in the
\texttt{report} directory at \url{https://github.com/umazalakain/fyp}.
All programs have been written for Agda 2.5.3.

Running \texttt{make modules} inside the \texttt{report} directory
will compile all Agda code present in this report and all of its
dependencies. The only required external library is Agda's standard
library, obtainable at \url{https://github.com/agda/agda-stdlib}.
(Instructions on how to install it can be found at
\url{https://agda.readthedocs.io/en/v2.5.3/tools/package-system.html#example-using-the-standard-library}.)

Running \texttt{make} inside the \texttt{report} directory first
compiles all source code and then generates a PDF file for the
report. During the course of this project I fixed a small bug that
made spacing of compiled literate Agda programs inconsistent and
disagreeable to the eye. The commit \texttt{8b83da6} can be
cherry-picked from Agda's master branch.

\chapter{User Guide}
%  Appendix C - User Guide This appendix should provide a detailed description
%  of how to use your system. In some cases, it may also be appropriate to
%  include a second guide dealing with maintenance and updating issues.

\end{appendices}

\end{document}
