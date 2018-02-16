\documentclass[12pt,a4paper]{scrreprt}

\usepackage[english]{babel}

% Equations
\usepackage{amsmath}

% Links and their colors
\usepackage[
  colorlinks=true,
  linkcolor=darkgray,
  citecolor=darkgray,
  urlcolor=darkgray
  ]{hyperref}

% And fonts
\urlstyle{rm}

% Type checking for Agda
\usepackage[conor,references]{agda}

% Fonts
\setmathsf{XITS Math}
% XITS doesn't have small caps
\setmainfont[
  Ligatures=TeX,
  SmallCapsFont={TeX Gyre Termes},
  SmallCapsFeatures={Letters=SmallCaps},
]{XITS}

% Less margins
\usepackage{fullpage}

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

% Commutative diagrams
\usepackage{tikz}


\begin{document}

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
        \todo{Remove borders}
        \includegraphics[width=3.5cm]{chi.png}
        \footnote{The Curry-Howard homeomorphism, by Luca Cardelli}
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

%   Introductory Pages Before the chapters of your report, there should be a
%   number of introductory pages. These should include:
%   - the title page (which has a compulsory format),
%   - a page giving an abstract of your work,
%   - an acknowledgements page, and
%   - a table of contents.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{abstract}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\todo{Abstract}
% Proving certain theorems can be boring and we want to automate it
% We don't want just the answer, we want a proof that it is the correct answer
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

Brief but intense, this project has also involved personal frustration
and self-doubt. It was on those occasions that my friends, both local
and remote, and my parents, on the other side of this planet, have
kept the ball rolling.

Needless to say, this project, of little importance to anyone but me,
is based on large amounts of previous science and countless hours of
accumulated human effort — a thought that still wonders me.

\tableofcontents

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Introduction}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%   Introduction This should briefly describe the problem which you
%   set out to solve and should essentially summarise the rest of your
%   report. The aim of an introduction is to convince the reader that
%   they should read on, so it is very important that excessive detail
%   is avoided at this stage.

%   The introduction should include the list of objectives that you
%   identified for the project, as well as a brief overview of the
%   outcome. In its final part, the introduction will usually outline
%   the structure of the rest of the report.

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

This project embarks upon constructing such solvers and proving them
correct. Three different problems will be considered: the first two
will involve solving equalities on algebraic structures, the third one
deciding a first-order predicate logic — Presburger arithmetic. The
aim is to better understand theorem proving as seen through the
Curry-Howard lens.

\todo{Four color theorem}
\todo{Comment on use cases}
\todo{Sections}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Background}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\todo{Present sections and their thoughtfulness}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Proofs as programs; propositions as types}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

If a computer is to verify the proof of some proposition, there must
exist some computational model for both proofs and propositions. One
such model was first devised by Haskell Curry \cite{Curry1934} and
later strengthened by William Alvin Howard \cite{Howard1980a}. It
establishes a two way correspondence between type theory and
intuitionistic logic: propositions are isomorphic to types and proofs
are to programs; to prove a proposition is to construct a program
inhabiting its corresponding type. Formal proofs can be verified by
type-checkers.

\todo{Agda 2.5.4 to fix whitespace}
\todo{Fix kerning}

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

    -- Disjunction
    data _⊎_ (A B : Set) : Set where
      inj₁ : A → A ⊎ B
      inj₂ : B → A ⊎ B

    module Laws {A : Set} where
      -- Ex falso quodlibet
      -- Agda can see there is no way of constructing ⊥
      explosion : ⊥ → Set
      explosion () -- No need to provide a case

      -- Law of non-contradiction
      -- AKA implication elimination
      -- AKA function application
      lnc : A → (A → ⊥) → ⊥
      lnc a a→⊥ = a→⊥ a

      -- No RAA in a constructive proof
      dne : ((A → ⊥) → ⊥) → A
      dne f = {!!} -- We need to manufacture an A, but we have none

      -- No LEM in a constructive proof
      lem : A ⊎ (A → ⊥)
      lem = {!!} -- To be or not to be demands a choice
\end{code}

Many variants exist on both sides of the isomorphism. The type theory
of simply typed lambda calculus — where $→$ is the only type
constructor — is in itself enough to model propositional logic. Type
theories containing dependent types — where the definition of a type
may depend on a value — model predicate logics containing quantifiers.
Further introduction to these ideas can be found at \cite{Wadler2015}.

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
rejected if they don't clearly show that they will eventually reach
termination. If we consider programs to be proofs, programs for which
termination cannot be verified should be rejected.

One way of showing termination is by always making recursive calls on
structurally smaller arguments. If data is defined inductively, this
assures that a base case is always eventually reached, and that
therefore recursion always eventually terminates.

\begin{code}
    -- Underscores show where the arguments go
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
rewriten by Ulf Norell in 2007. \cite{Norell2009} is an excellent
introduction; more in-depth documentation can be found at
\url{https://agda.readthedocs.io}. This section will only briefly
cover the basics required to familiarise the reader with what theorem
proving in Agda looks like.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{The experience of programming in Agda}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Development in Agda happens inside Emacs, and is a two way
conversation between the compiler and the programmer. Wherever a
definition is required, the user may instead write $?$ and request the
type-checker to reload the file. A ``hole'' will appear where the $?$
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Some peculiarities}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Arguments can be named, allowing subsequent arguments to depend on
them. If an argument can be inferred by the type-checker, the
programmer may choose to make it implicit by naming it and enclosing
it in curly braces. Implicit arguments can later still be explicitly
provided and pattern matched against. If the type of an argument can
be inferred by the type-checker, the programmer may omit it and use
$∀$:

\begin{code}
    -- All numbers are either even or not even
    prf₁ : ∀ {n} → Even n ⊎ (Even n → ⊥)
    prf₁ {zero} = inj₁ tt
    prf₁ {suc zero} = inj₂ λ b → b
    prf₁ {suc (suc n)} = prf₁ {n}
\end{code}

Multiple arguments sharing the same type can be grouped by providing
more than one name for them. With the exception of whitespace and a
few special symbols, names in Agda may contain arbitrary unicode
symbols. In addition, names can use underscores as placeholders for
any arguments they might receive.

\begin{code}
    ∣_-_∣ : (x y : ℕ) → ℕ
    ∣ zero - y ∣ = y
    ∣ suc x - zero ∣ = suc x
    ∣ suc x - suc y ∣ = ∣ x - y ∣
\end{code}

An anonymous function can be provided wherever a function is
expected. The programmer can pattern match against its arguments by
wrapping the arguments and body in curly brances.

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
    data Direction : Set where
      up    : Direction
      left  : Direction
      down  : Direction
      right : Direction
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
\end{code}

Whenever a datatype is pattern matched against, it will split into
those constructors capable of constructing that type:

\begin{code}
    -- Vec A n matches both constructors
    map : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
    map f [] = []
    map f (x ∷ xs) = f x ∷ map f xs

    -- Vec A (suc n) only matches _∷_
    head : {A : Set}{n : ℕ} → Vec A (suc n) → A
    head (x ∷ xs) = x
\end{code}

In Agda, pattern matching drives computation, and every case result of
it further refines the types in context.

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

If the type-checker can see that a type is impossible to construct,
pattern matching on it will render the case absurd, and thus there
will be no need to provide a definition for it.

\begin{code}
    -- The successor of an even number cannot be even
    prf₂ : ∀ n → {p : Even n} → Even (suc n) → ⊥
    prf₂ zero {p} ()
    prf₂ (suc zero) {()} sp
    prf₂ (suc (suc n)) {p} sp = prf₂ n {p} sp 
\end{code}

The type-checker uses dot patterns to show that pattern matching on
one argument uniquely implies another. If a value can be inferred by
the type checker, the user may replace it by an
underscore. Additionally, underscores can be used as non-binded
catch-alls outside of dot patterns on the left hand side of a
definition.

\begin{code}
    -- Pattern matching on xs determines n
    zipWith' : {A B C : Set} (n : ℕ) (f : A → B → C) → Vec A n → Vec B n → Vec C n
    zipWith' .zero f [] [] = []
    zipWith' .(suc _) f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith' _ f xs ys
\end{code}

With abstraction gives the programmer the ability to steer unification
in a particular direction by allowing them to pattern match on
arbitrary well-formed expressions on the left hand side of a
definition. This may result in the refinement of the rest of the
arguments. The following example is adapted from Agda-Stdlib and was
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
on \AgdaFunction{compare}~\AgdaBound{m}~\AgdaBound{n} we learn
about \AgdaBound{m} and \AgdaBound{n}. This is the difference between
with abstraction and ordinary case splitting on the right hand
side. \cite{Oury2008} contains other interesting examples of views.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Tools for reasoning}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Two terms of the same type are considered propositionally equal if
they unify with each other:

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

\AgdaRef{\_≡\_} is parametrised by an implicit type \AgdaBound{A} and
a value \AgdaBound{x}~\AgdaSymbol{:}~\AgdaBound{A} and indexed by a
value in \AgdaBound{A}. Given some fixed parameter \AgdaBound{x}, for
every
\AgdaBound{y}~\AgdaSymbol{:}~\AgdaBound{A}~\AgdaBound{x}~\AgdaDatatype{≡}~\AgdaBound{y}
is thus a type. The constructor \AgdaRef{refl} is the only means of
constructing a value of type
\AgdaBound{x}~\AgdaDatatype{≡}~\AgdaBound{y} and crucially, it can
only construct values where
\AgdaBound{x}~\AgdaDatatype{≡}~\AgdaBound{x} after normalisation.

\begin{code}
    -- Both sides normalise to suc (suc zero)
    prf₃ : (suc zero + suc zero) ≡ suc (suc zero)
    prf₃ = refl
\end{code}

We can now start writing functions that compute proofs that involve
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

\AgdaBound{n} \AgdaFunction{+} \AgdaRef{zero} cannot
normalise: because of how \AgdaRef{_+_} was defined, it needs to know
whether \AgdaBound{n} was constructed with \AgdaRef{zero} or
\AgdaRef{suc}. We can can advance the computation by pattern matching
on \AgdaBound{n}. While the base case is now trivial
(\AgdaRef{zero}~\AgdaFunction{+}~\AgdaRef{zero} unifies with
\AgdaRef{zero}), the problem persist in the inductive case, where
\AgdaRef{suc}~\AgdaSymbol{(}\AgdaBound{n}~\AgdaFunction{+}~\AgdaRef{zero}\AgdaSymbol{)}
has to unify with \AgdaRef{suc}~\AgdaBound{n}. By recursing on the
inductive hypothesis, we can unify
\AgdaBound{n}~\AgdaFunction{+}~\AgdaRef{zero} with \AgdaBound{n}, and
thus the remainder of the proof becomes trivial:

\begin{code}
    prf₅ zero = refl
    prf₅ (suc n) with n + zero | prf₅ n
    prf₅ (suc n) | .n          | refl = refl
\end{code}

This recursion on the induction hypothesis is common enough that there
is special syntax for it:

\begin{code}
    prf₆ : ∀ n → (n + zero) ≡ n
    prf₆ zero = refl
    prf₆ (suc n) rewrite prf₆ n = refl
\end{code}

Next, we introduce common reasoning tools enabling whiteboard-style
reasoning, all part of
\href{https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3767}{Agda-Stdlib}:

\begin{code}
    cong : {A B : Set}{x y : A} (f : A → B) → x ≡ y → f x ≡ f y
    cong f refl = refl

    module Reasoning {A : Set} where
      -- x and y unify when we pattern match on the first argument
      sym : ∀ {x y : A} → x ≡ y → y ≡ x
      sym refl = refl

      -- x and y unify when we pattern match on the first argument
      -- y ≡ z then becomes x ≡ z
      trans : ∀ {x y z : A} → x ≡ y → y ≡ z → x ≡ z
      trans refl eq = eq

      begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
      begin_ x≡y = x≡y

      _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
      _ ≡⟨⟩ x≡y = x≡y

      _≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
      _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

      _∎ : ∀ (x : A) → x ≡ x
      _∎ _ = refl

\end{code}
\AgdaHide{
\begin{code}
      infix  3 _∎
      infixr 2 _≡⟨⟩_ _≡⟨_⟩_
      infix  1 begin_

    open Reasoning
\end{code}
}

A trivial proof with an example of their usage:

\begin{code}
    prf₇ : ∀ l n m → ((zero + (l + zero)) + (n + zero)) + m ≡ (l + n) + m
    prf₇ l n m = begin
      (((zero + (l + zero)) + (n + zero)) + m)
        ≡⟨⟩
      (((l + zero) + (n + zero)) + m)
        ≡⟨ cong (λ t → (t + (n + zero)) + m) (prf₆ l) ⟩
      ((l + (n + zero)) + m)
        ≡⟨ cong (λ t → (l + t) + m) (prf₆ n) ⟩
      (l + n) + m
        ∎ 
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Proof by reflection}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\cite{Walt2012}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Problem solvers and their domains}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\todo{Forward reference solutions}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{A comment on Agda-Stdlib}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\url{https://agda.github.io/agda-stdlib/}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{A solver for monoids}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\AgdaHide{
\begin{code}
open import Data.Unit using (⊤ ; tt)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec using (Vec ; _∷_ ; [] ; tabulate ; lookup)
open import Data.Vec.N-ary using (N-ary)
open import Data.Fin.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.List.Pointwise using (decidable-≡)
open import Relation.Nullary using (yes ; no)
open ≡-Reasoning
\end{code}
}

Monoids are a common algebraic structure found as part of many
problems. A monoid solver is an automated proof generator which can
be used wherever an equation on monoids must be proved. Constructing
one is a good first approach to building automated solvers: it lacks
the complexity of many other problems but has the same high-level
structure.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Problem description and specification}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\href{https://agda.github.io/agda-stdlib/Algebra.html#1079}{Agda-Stdlib's
definition of a monoid} is based on notions about many other algebraic
structures, and is therefore fairly complex. We will instead use our
own definition, which is entirely self-contained and fairly simple.

\begin{code}
-- A monoid is a set
record Monoid (M : Set) : Set where
  infix 25 _·_
  field
    -- Together with an associative binary operation
    _·_ : M → M → M
    law-·-· : (x y z : M) → (x · y) · z ≡ x · (y · z)
    -- And a neutral element absorbed on both sides
    ε : M
    law-ε-· : (m : M) → ε · m ≡ m
    law-·-ε : (m : M) → m ≡ m · ε
\end{code}

\AgdaRef{M}, the set on which the monoid is defined, is often referred
to as the carrier. $(ℕ, +, 0)$ and $(ℕ, ·, 1)$ are both examples of
monoids. Note however that these also happen to be commutative, while
monoids need not be — more on solving commutative monoids later. An
example of a non-commutative monoid are lists together with the
concatenation operation:

\begin{code}
open import Data.List using (List ; [] ; _∷_ ; _++_)

LIST-MONOID : (T : Set) → Monoid (List T)
LIST-MONOID T = record
              { ε = []
              ; _·_ = _++_
              ; law-ε-· = λ xs → refl
              ; law-·-ε = right-[]
              ; law-·-· = assoc
              } where
              
              right-[] : (xs : List T) → xs ≡ xs ++ []
              right-[] [] = refl
              right-[] (x ∷ xs) = cong (x ∷_) (right-[] xs)
              
              assoc : (xs ys zs : List T) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
              assoc [] ys zs = refl
              assoc (x ∷ xs) ys zs rewrite assoc xs ys zs = refl
\end{code}

An equation on monoids cannot be decided by unification alone: the
monoid laws show that definitionally distinct propositions might in
fact have the same meaning.

\begin{code}
eqn₁ : {T : Set}(xs : List T) → [] ++ xs ≡ xs ++ []
eqn₁ {T} xs = begin
  [] ++ xs
    ≡⟨ law-ε-· xs ⟩
  xs
    ≡⟨ law-·-ε xs ⟩
  xs ++ []
    ∎
  where open Monoid (LIST-MONOID T) 
\end{code}

Without an automated solver, the number of law applications and hence
the length of the proof grows linearly with respect to the size of the
monoid. An automated solver should allow us to effortlessly satisfy a
proposition like the following:

\begin{code}
eqn₂ : {T : Set}(xs ys zs : List T)
     → (xs ++ []) ++ ([] ++ (ys ++ (ys ++ zs)))
     ≡ xs ++ ((ys ++ ys) ++ (zs ++ []))

eqn₂ xs ys zs = begin
  (xs ++ []) ++ ([] ++ (ys ++ (ys ++ zs)))
    ≡⟨ cong (_++ ([] ++ (ys ++ (ys ++ zs)))) (sym (law-·-ε xs)) ⟩
  xs ++ ([] ++ (ys ++ (ys ++ zs)))
    ≡⟨ cong (xs ++_) (law-ε-· (ys ++ (ys ++ zs))) ⟩
  xs ++ (ys ++ (ys ++ zs))
    ≡⟨ cong (xs ++_) (sym (law-·-· ys ys zs)) ⟩
  xs ++ ((ys ++ ys) ++ zs)
    ≡⟨ cong (λ zs' → xs ++ ((ys ++ ys) ++ zs')) (law-·-ε _) ⟩
  xs ++ ((ys ++ ys) ++ (zs ++ []))
    ∎
  where open Monoid (LIST-MONOID _)
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Design and implementation}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

A proposition containing variables and monoid operators can be
normalised into a canonical form. The characteristics that make two
propositions definitionally distinct — when they are, in fact, equal
in meaning — can be eliminated. It is crucial that this process —
normalisation — guarantees the preservation of meaning. After
normalisation, the two results can be compared: if they are equal, so
must the original propositions be. This is the sketch of the procedure
we are implementing.

\todo{What about proving it complete?}

The procedure requires some notion of the equation it is trying to
solve. We use an abstract syntax tree to represent equations and
finite indices to refer to variables — the
type \AgdaDatatype{Fin}~\AgdaBound{n} contains \AgdaBound{n} distinct
values. Moreover, we use a type parameter on \AgdaRef{Eqn} to
\textit{push in} this limitation on the number of indices.

\begin{code}
data Expr (n : ℕ) : Set where
  var' : Fin n           → Expr n
  ε'   :                   Expr n
  _·'_ : Expr n → Expr n → Expr n

data Eqn (n : ℕ) : Set where
  _≡'_ : Expr n → Expr n → Eqn n
\end{code}

Let us use an example to help us come up with a suitable normal
form. Consider the following two expressions:
\begin{align*}
    P &= ((ε · x) · (x · y))  &  Q &= ((x · x) · y) \\
    \intertext{Neutral elements do not have any meaning and can be
    absorbed:}
    P &= (x · (x · y))        &  Q &= ((x · x) · y) \\
    \intertext{Elements can always be re-associated and thus
    association does not have any meaning and can be removed:}
    P &= x · x · y            &  Q &= x · x · y     \\
\end{align*}
We can now see that both propositions are equal. It is important to
note that these are not commutative monoids, and that thus the order
of elements matters.

Lists are a suitable data structure for representing flat elements —
indices here — that can appear multiple times and whose order
carries meaning. If we were dealing with commutative monoids, where
order does carry meaning, a matrix of indices and number of
occurrences could be represented as a vector of integers — where the
position in the matrix represents the index and the content represents
the number of occurrences.

\begin{code}
NormalForm : ℕ → Set
NormalForm n = List (Fin n)
\end{code}

The normalising function is trivial:

\begin{code}
normalise : ∀ {n} → Expr n → NormalForm n
normalise (var' x) = x ∷ []
normalise ε' = []
normalise (i ·' j) = normalise i ++ normalise j
\end{code}

From here on, we will work with a concrete monoid (\AgdaBound{monoid})
on a concrete carrier \AgdaBound{M}. This results in all of the
definitions within having \AgdaRef{M} and \AgdaRef{monoid}
defined. When called from the outside of this module, these
definitions will have
\AgdaSymbol{\{}\AgdaBound{M}~\AgdaSymbol{:}~\AgdaPrimitiveType{Set}\AgdaSymbol{\}}~\AgdaSymbol{(}\AgdaBound{monoid}~\AgdaSymbol{:}~\AgdaRecord{Monoid}~\AgdaBound{M}\AgdaSymbol{)}
prepended to their type. We can also make the insides of
\AgdaRef{monoid} directly accessible by opening it as if it were a
module.

\begin{code}
module _ {M : Set} (monoid : Monoid M) where
  open Monoid monoid
\end{code}

To evaluate an expression, we need a concrete assignment for the
variables contained within. We call this an environment. An
environment is a lookup table where each of the indices has an
associated value in the carrier.
The size of \AgdaDatatype{Fin}~\AgdaBound{n} is equal to the size
of \AgdaDatatype{Vec}~\AgdaBound{M}~\AgdaBound{n}, and so we can map
every element in \AgdaDatatype{Fin}~\AgdaBound{n} to a value
in \AgdaDatatype{Vec}~\AgdaBound{M}~\AgdaBound{n}.

\begin{code}
  Env : ℕ → Set
  Env n = Vec M n
\end{code}

Once we have expressions, normal forms end environments, we can define
what it is to be evaluated for both expressions and normal forms. Note
that both expressions and normal forms cannot contain more indices
than the environment has — every index has to have assigned a value.

\begin{code}
  -- lookup x ρ ≔ get value at position x in ρ
  ⟦_⟧ : ∀ {n} → Expr n → Env n → M
  ⟦ var' x ⟧   ρ = lookup x ρ
  ⟦ ε' ⟧       ρ = ε
  ⟦ xs ·' ys ⟧ ρ = ⟦ xs ⟧ ρ · ⟦ ys ⟧ ρ

  ⟦_⇓⟧ : ∀ {n} → NormalForm n → Env n → M
  ⟦ [] ⇓⟧       ρ = ε
  ⟦ (x ∷ xs) ⇓⟧ ρ = (lookup x ρ) · ⟦ xs ⇓⟧ ρ
\end{code}

\begin{tikzpicture}[node distance=4cm,line width=1pt]
  \node (E)                             {\AgdaDatatype{Expr}~\AgdaBound{n}};
  \node (N)             [below of=E]    {\AgdaDatatype{NormalForm}~\AgdaBound{n}};
  \node (M)             [right of=N]    {\AgdaBound{M}};
  \draw[->] (E) to node [sloped, below] {\AgdaFunction{normalise}}  (N);
  \draw[->] (N) to node [sloped, below] {\AgdaFunction{⟦\_⇓⟧}}      (M);
  \draw[->] (E) to node [sloped, above] {\AgdaFunction{⟦\_⟧}}       (M);
\end{tikzpicture}

\begin{code}
  eval-distr : ∀ {n} (p q : NormalForm n) → (ρ : Env n)
               → ⟦ p ⇓⟧ ρ · ⟦ q ⇓⟧ ρ ≡ ⟦ p ++ q ⇓⟧ ρ

  eval-distr [] q ρ = law-ε-· _
  eval-distr (x ∷ p) q ρ = begin
    ((lookup x ρ) · ⟦ p ⇓⟧ ρ) · ⟦ q ⇓⟧ ρ
      ≡⟨ law-·-· _ _ _ ⟩
    (lookup x ρ) · (⟦ p ⇓⟧ ρ · ⟦ q ⇓⟧ ρ)
      ≡⟨ cong (_·_ (lookup x ρ)) (eval-distr p q ρ) ⟩
    (lookup x ρ) · ⟦ p ++ q ⇓⟧ ρ
      ∎

  eval-commutes : ∀ {n} → (expr : Expr n) → (ρ : Env n)
                  → ⟦ expr ⟧ ρ ≡ ⟦ normalise expr ⇓⟧ ρ

  eval-commutes (var' x) ρ = law-·-ε _
  eval-commutes ε'       ρ = refl
  eval-commutes (p ·' q) ρ
    rewrite eval-commutes p ρ | eval-commutes q ρ
    = eval-distr (normalise p) (normalise q) ρ
\end{code}

\begin{code}
  Solution : ∀ {n} → Eqn n → Set
  Solution {n} (p ≡' q) with decidable-≡ _≟_ (normalise p) (normalise q)
  ... | no _ = ⊤
  ... | yes _ = ∀ (ρ : Env n) → ⟦ p ⟧ ρ ≡ ⟦ q ⟧ ρ

  solve : ∀ {n} (eqn : Eqn n) → Solution eqn
  solve (p ≡' q) with decidable-≡ _≟_ (normalise p) (normalise q)
  ...            | no _ = tt
  ...            | yes leq = λ ρ → 
    ⟦ p ⟧ ρ
      ≡⟨ eval-commutes p ρ ⟩
    ⟦ normalise p ⇓⟧ ρ
      ≡⟨ cong (λ x → ⟦ x ⇓⟧ ρ) leq  ⟩
    ⟦ normalise q ⇓⟧ ρ
      ≡⟨ sym (eval-commutes q ρ) ⟩
    ⟦ q ⟧ ρ
      ∎
\end{code}

\begin{code}
-- Cite magic

_$ⁿ_ : ∀ {n}{A B : Set} → N-ary n A B → (Vec A n → B)
f $ⁿ [] = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs

vars : ∀ {n} → Vec (Expr n) n
vars = tabulate var'

build : ∀ {A}(n : ℕ) → N-ary n (Expr n) A → A
build n f = f $ⁿ vars {n}

\end{code}

\begin{code}
eqn₂-auto : {T : Set}(xs ys zs : List T)
          → (xs ++ []) ++ ([] ++ (ys ++ (ys ++ zs)))
          ≡ xs ++ ((ys ++ ys) ++ (zs ++ []))

eqn₂-auto xs ys zs = solve (LIST-MONOID _) (build 3 λ xs ys zs
                   → ((xs ·' ε') ·' (ε' ·' (ys ·' (ys ·' zs))))
                   ≡' (xs ·' ((ys ·' ys) ·' (zs ·' ε')))) (xs ∷ ys ∷ zs ∷ [])
\end{code}

\todo{mention quoting}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{A solver for commutative rings}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

- What is a commutative ring?
- Horner normal form + constraints

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{A solver for Presburger arithmetic}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

- What Presburger arithmetic is
- The three ways of solving it
- What ways we chose, and why
- How to do this in Agda, what the benefits are
- High level plan of the module
    - Representation
    - Normalisation
    - Evaluation
    - Correctness proofs
    - Quoting

\chapter{Verification and validation}

\todo{Dependent types, higher standards, no tests, we formally describe what correct is}

%   Verification and Validation In this section you should outline the
%   verification and validation procedures that you've adopted throughout the
%   project to ensure that the final product satisfies its specification. In
%   particular, you should outline the test procedures that you adopted during
%   and after implementation. Your aim here is to convince the reader that the
%   product has been thoroughly and appropriately verified. Detailed test
%   results should, however, form a separate appendix at the end of the report.

- Why is this absolutely correct, Agda?

% \chapter{Results and evaluation}

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

% \chapter{Related work}

%   Related Work You should survey and critically evaluate other work which you
%   have read or otherwise considered in the general area of the project topic.
%   The aim here is to place your project work in the context of the related
%   work.

% \chapter{Summary and conclusions}

%   Summary and Conclusions In the final chapter of your report, you should
%   summarise how successful you were in achieving the original project
%   objectives, what problems arose in the course of the project which could not
%   be readily solved in the time available, and how your work could be
%   developed in future to enhance its utility. It is OK to be upbeat,
%   especially if you are pleased with what you have achieved!

\bibliographystyle{apalike}
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

% \chapter{Detailed Specification and Design}
%   Appendix A - Detailed Specification and Design This appendix should contain
%   the details of your project specification that were not included in the main
%   body of your report.

% \chapter{Detailed Test Strategy and Test Cases}
%   Appendix B - Detailed Test Strategy and Test Cases This appendix should
%   contain the details of the strategy you used to test your software, together
%   with your tabulated and commented test results.

% \chapter{User Guide}
%   Appendix C - User Guide This appendix should provide a detailed description
%   of how to use your system. In some cases, it may also be appropriate to
%   include a second guide dealing with maintenance and updating issues.

\end{document}
