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

% Diagrams
\usepackage{tikz}
\usetikzlibrary{positioning}

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

\todo{check spelling}
\todo{claims}
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

Brief but intense, this project has also involved — and been affected
by — personal frustration and self-doubt. It was on those occasions
that my friends, both local and remote, and my parents, on the other
side of this planet, have kept the ball rolling.

Needless to say, this project, of little importance to anyone but me,
is based on large amounts of previous science and countless hours of
accumulated human effort — a thought that still impresses me.

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

\todo{Main results}
\todo{Comment on use cases}
\todo{Link verification}
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
      explosion : ⊥ → A
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

This interactive way of programming, often described as ``hole
driven'', allows the programmer to work with partial definitions and
to receive constant feedback from the type-checker.

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
these parameters are named:

\begin{code}
    data List (A : Set) : Set where
      []  :              List A
      _∷_ : A → List A → List A
\end{code}

Moreover, datatypes can be indexed. Each of these indices is said to
introduce a family of types. Constructors do not need to keep within
the same index, and may in fact \textit{jump} from one to another.
Parameters are forced on datatypes, but indices are a choice.

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
\subsection{Reasoning tools}
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
every \AgdaBound{y}~\AgdaSymbol{:}~\AgdaBound{A} there is a
type \AgdaBound{x}~\AgdaDatatype{≡}~\AgdaBound{y}. The
constructor \AgdaRef{refl} is the only means of constructing a value
of type \AgdaBound{x}~\AgdaDatatype{≡}~\AgdaBound{y} and crucially, it
can only construct values
where \AgdaBound{x}~\AgdaDatatype{≡}~\AgdaBound{x} after
normalisation.

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
normalise: because of how \AgdaRef{\_+\_} was defined, it needs to know
whether \AgdaBound{n} was constructed with \AgdaRef{zero} or
\AgdaRef{suc}. We can can advance the computation by pattern matching
on \AgdaBound{n}. While the base case is now trivial
(\AgdaRef{zero}~\AgdaFunction{+}~\AgdaRef{zero} unifies with
\AgdaRef{zero}), the problem persists in the inductive case, where
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

We can now leave a record of type rewrites and their justifications:

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

Procedures that generate proofs often require to a notion of what
their target theorem is. This notion has to be translated — reflected
— into a data structure in a source language that the procedure can
manipulate. The proof that the procedure will then construct will
depend on this data structure.

\href{https://agda.readthedocs.io/en/latest/language/reflection.html}{
The support for reflection that Agda offers} gives the programmer the
ability to ``quote'' arbitrary parts of the program into abstract
terms that represent them. In the other direction, these abstract
terms can be procedurally built and later ``unquoted'' into concrete
Agda code. Additionally, Agda also offers means to directly control
type checking and unification.

Reflection is most commonly used to create ``tactics'' that
programmatically proof propositions. For this common use case, Agda
provides ``macros'': functions that take as an argument the quoted
hole they must solve and handle back some computation that solves
it. The next example, extracted from Agda's documentation, shows how
the macro ~\AgdaFunction{by-magic}~ uses ~\AgdaFunction{magic}~ to
construct values of a given type. Note that ~\AgdaFunction{magic}~
returns a ~\AgdaDatatype{Term}~ inside a ~\AgdaDatatype{TC}~ monad:
this allows ~\AgdaFunction{magic}~ to throw type errors if the type
supplied to it is outside of its problem domain.

\AgdaHide{
\begin{code}
module _ where
  private
    open import Agda.Builtin.Unit
    open import Agda.Builtin.Reflection
\end{code}
}

\begin{code}
    magic : Type → TC Term
    magic = {!!}

    macro
      by-magic : Term → TC ⊤
      by-magic hole =
        bindTC (inferType hole) λ goal →
        bindTC (magic goal) λ solution →
        unify hole solution
\end{code}

Both \cite{Walt2012} and \cite{VanDerWalt2012} are in-depth
introductions to Agda's reflection mechanisms and come with several
example use cases. \cite{Kokke2015} uses reflection to, given a list
of rules, conduct automatic first-order proof search on a goal type.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Builtins, Stdlib and Prelude}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Agda is distributed together with a
\href{https://agda.readthedocs.io/en/latest/language/built-ins.html}{set
of builtin data types and functions} found under the
\AgdaModule{Agda.Builtin}~module. These builtin types get special
treatment during compilation but can nevertheless be easily redefined
and customised by the user. \AgdaModule{Agda.Builtin}~does not provide
the user with any proofs of the properties related to the data types
it contains.

The development of
\href{https://github.com/agda/Agda-Stdlib}{Agda-Stdlib} happens in
close coordination with Agda's. Unlike \AgdaModule{Agda.Builtin}'s
conservative approach, Agda-Stdlib provides a large library of
commonly used data structures and functions. It abstracts
aggressively which, together with its heavy use of unicode symbols and
infix notation, can often result in code challenging for the
unexperienced reader. Along with the data types it provides there come
proofs for many of their common properties.

In comparison,
\href{https://github.com/ulfnorell/agda-prelude}{Agda-Prelude} is less
abstract and more readable and efficient, but not as complete.  For
that reason, this project will make use of the tools provided by
Agda-Stdlib.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Problem solvers and their domains}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\todo{Forward reference backgrounds}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Solving monoids}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\AgdaHide{
\begin{code}
module Monoids where
  private
    open import Data.Unit using (⊤ ; tt)
    open import Data.List using (List ; [] ; _∷_)
    open import Data.Nat using (ℕ ; zero ; suc ; _+_)
    open import Data.Fin using (Fin ; zero ; suc)
    open import Data.Vec using (Vec ; _∷_ ; [] ; tabulate ; lookup)
    open import Data.Vec.N-ary using (N-ary)
    open import Data.Fin.Properties renaming (_≟_ to _Fin-≟_)
    open import Relation.Binary.PropositionalEquality
    open import Relation.Binary using (Decidable)
    open import Relation.Binary.List.Pointwise using () renaming (decidable-≡ to List-≟)
    open import Relation.Nullary using (yes ; no)
    open ≡-Reasoning
\end{code}
}

Monoids are common algebraic structures involved in many problems. A
monoid solver is an automated proof generator which can be used to
prove an equation on monoids. Constructing such a solver is a good
first approach to proof automation: it lacks the complexity of many
other problems while it has their same high-level structure.

\todo{Boutin's paper}

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
\section{A verified decision procedure}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

A proposition containing variables and monoid operators can be
normalised into a canonical form. The characteristics that make two
propositions definitionally distinct — when they are, in fact, equal
in meaning — can be eliminated. It is crucial that this process —
normalisation — guarantees the preservation of meaning. After
normalisation, the two results can be compared: if they are equal, so
must the original propositions be. This is the sketch of the procedure
we are implementing.

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
    \intertext{Elements can always be re-associated: association does
    not have any meaning and can be removed:}
    P &= x · x · y            &  Q &= x · x · y     \\
\end{align*}
We can now see that both propositions are equal. It is important to
note that these are not commutative monoids, and that thus the order
of the elements matters.

Lists are a suitable data structure for representing flat elements —
indices here — that can appear multiple times and whose order
carries meaning. If we were dealing with commutative monoids, where
order does not carry meaning, a matrix of indices and the number of
occurrences of each could be represented as a vector of integers —
where the position in the vector represents the index and the content
represents the number of occurrences.

\begin{code}
    NormalForm : ℕ → Set
    NormalForm n = List (Fin n)
\end{code}

\AgdaHide{
\begin{code}
    _≟_ : ∀ {n} → Decidable {A = List (Fin n)} _≡_
    _≟_ = List-≟ _Fin-≟_ 
\end{code}
}

The normalising function ignores neutral elements and preserves order:

\begin{code}
    normalise : ∀ {n} → Expr n → NormalForm n
    normalise (var' i)   = i ∷ []
    normalise ε'         = []
    normalise (e₁ ·' e₂) = normalise e₁ ++ normalise e₂
\end{code}

From here on, we will work with a concrete monoid (\AgdaBound{monoid})
on a concrete carrier \AgdaBound{M}. This results in all of the
definitions inside of the module having \AgdaBound{M} and
\AgdaBound{monoid} defined. When called from the outside of this
module, these definitions will have
\AgdaSymbol{\{}\AgdaBound{M}~\AgdaSymbol{:}~\AgdaPrimitiveType{Set}\AgdaSymbol{\}}~\AgdaSymbol{(}\AgdaBound{monoid}~\AgdaSymbol{:}~\AgdaRecord{Monoid}~\AgdaBound{M}\AgdaSymbol{)}
prepended to their type. We can also make the insides of
\AgdaBound{monoid} directly accessible by opening it as if it were a
module.

\begin{AgdaAlign}
\begin{code}
    module _ {M : Set} (monoid : Monoid M) where
      open Monoid monoid
\end{code}

To evaluate an expression we need a concrete assignment for the
variables contained within. We call this an environment. An
environment is a lookup table where each of the indices has an
associated value in the carrier \AgdaBound{M}.
The size of \AgdaDatatype{Fin}~\AgdaBound{n} is equal to the size
of \AgdaDatatype{Vec}~\AgdaBound{M}~\AgdaBound{n}, and so we can
define a bijection between \AgdaDatatype{Fin}~\AgdaBound{n}
and \AgdaDatatype{Vec}~\AgdaBound{M}~\AgdaBound{n}.

\begin{code}
      Env : ℕ → Set
      Env n = Vec M n
\end{code}

Once we have expressions, normal forms end environments, we can define
what the evaluation of both — expressions and normal forms — is. Note
that both definitions rule out expressions and normal forms with more
indices than the environment contains — every index within the
expression has to have a corresponding value in the environment.

\begin{code}
      -- lookup x ρ ≔ value at index x in ρ
      ⟦_⟧ : ∀ {n} → Expr n → Env n → M
      ⟦ var' i ⟧   ρ = lookup i ρ
      ⟦ ε' ⟧       ρ = ε
      ⟦ e₁ ·' e₂ ⟧ ρ = ⟦ e₁ ⟧ ρ · ⟦ e₂ ⟧ ρ

      ⟦_⇓⟧ : ∀ {n} → NormalForm n → Env n → M
      ⟦ [] ⇓⟧      ρ = ε
      ⟦ (i ∷ e) ⇓⟧ ρ = (lookup i ρ) · ⟦ e ⇓⟧ ρ
\end{code}

We are finally ready to make our claim: an equation on monoids holds
provided that both sides of the equation match after
normalisation. We cannot make any claims in the other direction — if
both sides do not equal after normalisation the equation must be
false. This can most clearly be seen by taking the unit type (the type
with a single value) as carrier of the monoid: all equations are true,
yet the monoid laws allow to prove only some of them. Because we
cannot make any interesting claims, we can claim true the trivial.

\begin{code}
      Solution : ∀ {n} → Eqn n → Set
      Solution {n} (e₁ ≡' e₂) with (normalise e₁) ≟ (normalise e₂)
      ...                     | no  _ = ⊤
      ...                     | yes _ = ∀ (ρ : Env n) → ⟦ e₁ ⟧ ρ ≡ ⟦ e₂ ⟧ ρ
\end{code}

We define decidable equality of normal forms (here \AgdaRef{\_≟\_})
by relying on the definitions of decidable equality of lists and
finite indices.

\AgdaRef{Solution}~ returns an appropriate per-equation specification
for every ~\AgdaDatatype{Eqn}~\AgdaBound{n}. We must now prove that we
are able to meet such specifications.

\begin{code}
      solve : ∀ {n} (eqn : Eqn n) → Solution eqn
\end{code}

The crux of such a proof is to show that the evaluation of an
expression can be decomposed into the normalisation into a normal form
and its posterior evaluation.

\begin{code}
      eval-commutes : ∀ {n} → (e : Expr n) → (ρ : Env n)
                      → ⟦ e ⟧ ρ ≡ ⟦ normalise e ⇓⟧ ρ
\end{code}

Put in a diagrammatic form, we must show that the following commutes:

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

Once we are able to show that they are, indeed, extensionally equal,
we can translate the evaluation of expressions into the evaluation of
normal forms, and then use congruence to proof that two equal normal
forms must evaluate to equal values.

\begin{code}
      solve (e₁ ≡' e₂) with (normalise e₁) ≟ (normalise e₂)
      ...            | no  _  = tt
      ...            | yes eq = λ ρ → 
        ⟦ e₁ ⟧ ρ
          ≡⟨ eval-commutes e₁ ρ ⟩
        ⟦ normalise e₁ ⇓⟧ ρ
          ≡⟨ cong (λ e₌ → ⟦ e₌ ⇓⟧ ρ) eq  ⟩
        ⟦ normalise e₂ ⇓⟧ ρ
          ≡⟨ sym (eval-commutes e₂ ρ) ⟩
        ⟦ e₂ ⟧ ρ
          ∎
\end{code}

Showing \AgdaRef{eval-commutes} is done inductively and it requires a
proof that concatenation of normal forms (\AgdaRef{\_++\_}) preserves
the structure of monoids. Note that these proofs, perhaps
unsurprisingly, use all of the monoid laws.

\begin{code}
      eval-homo : ∀ {n} (e₁ e₂ : NormalForm n) → (ρ : Env n)
                  → ⟦ e₁ ⇓⟧ ρ · ⟦ e₂ ⇓⟧ ρ ≡ ⟦ e₁ ++ e₂ ⇓⟧ ρ

      eval-homo []       e₂ ρ = law-ε-· (⟦ e₂ ⇓⟧ ρ)
      eval-homo (i ∷ e₁) e₂ ρ = begin
        ((lookup i ρ) · ⟦ e₁ ⇓⟧ ρ) · ⟦ e₂ ⇓⟧ ρ
          ≡⟨ law-·-· _ _ _ ⟩
        (lookup i ρ) · (⟦ e₁ ⇓⟧ ρ · ⟦ e₂ ⇓⟧ ρ)
          ≡⟨ cong (_·_ (lookup i ρ)) (eval-homo e₁ e₂ ρ) ⟩
        (lookup i ρ) · ⟦ e₁ ++ e₂ ⇓⟧ ρ
          ∎

      -- eval-commutes : ∀ {n} → (e : Expr n) → (ρ : Env n)
      --                 → ⟦ e ⟧ ρ ≡ ⟦ normalise e ⇓⟧ ρ
      eval-commutes ε'         ρ = refl
      eval-commutes (var' x)   ρ = law-·-ε (lookup x ρ)
      eval-commutes (e₁ ·' e₂) ρ rewrite eval-commutes e₁ ρ
                                         | eval-commutes e₂ ρ
                                         = eval-homo (normalise e₁) (normalise e₂) ρ
\end{code}
\end{AgdaAlign}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Results and usage}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We can now automatically generate proofs for arbitrary equations on monoids:

\begin{code}
    eqn₁-auto : {T : Set}(xs : List T) → [] ++ xs ≡ xs ++ []
    eqn₁-auto xs = solve (LIST-MONOID _)
                   ((ε' ·' var' zero) ≡' (var' zero ·' ε')) (xs ∷ [])
\end{code}

However, we still need to manually build the expressions representing
the target theorem. This includes handling the indices referring to
variables appropriatly. As shown by \cite{Bove2009} at
\url{http://www.cse.chalmers.se/~ulfn/code/tphols09/}, index
referrences can be set up automatically, partially alleviating this
problem and resulting in the following usage:

\AgdaHide{
\begin{code}
    _$ⁿ_ : ∀ {n}{A B : Set} → N-ary n A B → (Vec A n → B)
    f $ⁿ [] = f
    f $ⁿ (x ∷ xs) = f x $ⁿ xs
    
    vars : ∀ {n} → Vec (Expr n) n
    vars = tabulate var'

    build : ∀ {A}(n : ℕ) → N-ary n (Expr n) A → A
    build n f = f $ⁿ vars {n}
\end{code}
}

\begin{code}
    eqn₂-auto : {T : Set}(xs ys zs : List T)
              → (xs ++ []) ++ ([] ++ (ys ++ (ys ++ zs)))
              ≡ xs ++ ((ys ++ ys) ++ (zs ++ []))
    
    eqn₂-auto xs ys zs = solve (LIST-MONOID _) (build 3 λ xs ys zs
                       → ((xs ·' ε') ·' (ε' ·' (ys ·' (ys ·' zs))))
                       ≡' (xs ·' ((ys ·' ys) ·' (zs ·' ε')))) (xs ∷ ys ∷ zs ∷ [])
\end{code}

Agda's support for reflection can be used to build a macro that
inspects the type of the goal and translates it into a data structure
that the proof generating procedure can understand. This would result
in the following example usage:

\AgdaHide{
\begin{code}
    postulate
      magic-solve : {T : Set} (m : Monoid (List T)) (xs ys zs : List T)
                    → (xs ++ []) ++ ([] ++ (ys ++ (ys ++ zs)))
                    ≡ xs ++ ((ys ++ ys) ++ (zs ++ []))
\end{code}
}

\begin{code}
    eqn₂-magic : {T : Set}(xs ys zs : List T)
               → (xs ++ []) ++ ([] ++ (ys ++ (ys ++ zs)))
               ≡ xs ++ ((ys ++ ys) ++ (zs ++ []))

    eqn₂-magic = magic-solve (LIST-MONOID _)
\end{code}

\todo{forward reference general verification}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Solving commutative rings}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Problem description and specification}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Design and implementation}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\cite{Gregoire2005}
\cite{Boutin1997}

- What is a commutative ring?
- Horner normal form + constraints

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Solving Presburger arithmetic}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\todo{Note that there is no such thing in Agda}

In 1929, Mojżesz Presburger presented and proved decidable a predicate
logic on natural numbers (expandable to integers and real numbers)
with addition as its only operation. The original paper
\cite{Presburger1929} is in Polish and uses outdated notation;
\cite{Stansifer1984} contains an English translation and comments
clarifying the original. Several procedures capable of deciding
Presburger arithmetic exist, some of them are introduced
later on. Nevertheless, \cite{Fischer1974} showed that the worst case
of any such procedure has a doubly exponential run time.

Here are some example simple predicates that better illustrate the
expressiveness of Presburger arithmetic.

\begin{align}
∀x.\:∃y.\:x=2y\,∨\,x=2y+1 \label{eq:even-or-odd} \\
∀x.\:¬∃y.\:2x=2y+1                               \\
∀x.\:4|x\,⇒\,2|x                                 \\
∀x.\:x\,<\,x + 1
\end{align}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Problem description and specification}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

To solve Presburger arithmetic is to create a verified procedure
capable of deciding any well-formed Presburger predicate where all
variables are bound. Without an automated procedure, proving a
predicate like~\ref{eq:even-or-odd} can already become burdensome:

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

\todo{Add definition of ∃ and +-suc to annex}

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

\AgdaHide{
\begin{code}
module Presburger where
  open import Function using (id ; _∘_)
  open import Data.Fin using (Fin ; zero ; suc)
  open import Data.Integer as Int using (ℤ ; +_ ; -[1+_] ; _+_ ; _-_ ; -_ ; _*_ ; _<_ ; _≤_ ; _>_)
  open import Data.Nat as Nat using (ℕ ; zero ; suc)
  open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
  open import Data.Vec as Vec using (Vec ; [] ; _∷_)
  open import Data.List as List using (List ; [] ; _∷_ ; _++_)
  open import Data.Maybe using (Maybe ; nothing ; just)
  open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂ ; uncurry)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; cong ; sym ; _≢_)
  open import Relation.Nullary using (Dec ; yes ; no)
  open import Data.Integer.Properties as IntProp
  open import Relation.Binary using (Tri)
  open import Data.List.All using (All ; [] ; _∷_)
  open import Data.Unit using (⊤ ; tt)
  open import Data.Bool using (Bool ; true ; false ; T ; not ; _∨_)
  open import Data.Empty using (⊥)
  open import Data.Nat.DivMod using (_div_)

  open import Prologue using (_<?_ ; ×-list)
\end{code}
}

From here on, we will assume the following syntax for Presburger
predicates:

\begin{code}
  data Atom (i : ℕ) : Set where
    num' : ℤ               → Atom i
    _+'_ : Atom i → Atom i → Atom i
    _*'_ : ℤ      → Atom i → Atom i
    var' : Fin i           → Atom i
                            
  data Rel : Set where
    <' >' ≤' ≥' =' : Rel
  
  data Formula (i : ℕ) : Set where
    -- Divisibility
    _∣'_           : ℕ → Atom i            → Formula i
    _[_]_          : Atom i → Rel → Atom i → Formula i
    _∧'_ _∨'_ _⇒'_ : Formula i → Formula i → Formula i
    ¬'_            : Formula i             → Formula i
    -- New variable introduction
    ∃'_ ∀'_        : Formula (suc i)       → Formula i
\end{code}

We use de Bruijn \cite{Bruijn1972} indices to refer to bindings by
their proximity: a variable with index \AgdaNumber{0} refers to the
most immediate binding to the left; index \AgdaBound{n} refers to the
binding introduced \AgdaBound{n} bindings away. Using de Bruijn
indices instead of variable names has two main advantages:

\begin{itemize}[noitemsep]
  \item there is no need to rename variables on substitution; and
  \item the choice of variable names does not affect equality.
\end{itemize}

For any formula of type ~\AgdaDatatype{Formula}~\AgdaBound{n},
\AgdaBound{n} indicates the number variables introduced outside of the
formula. Quantifiers ~\AgdaInductiveConstructor{∀'\_}~ and
~\AgdaInductiveConstructor{∃'\_} make a new variable available to their
arguments.

Theorem~\ref{eq:even-or-odd} can be transcribed as follows:

\begin{code}
  pred₁' : Formula 0
  pred₁' = ∀' ∃' ((x [ =' ] ((+ 2) *' y))
              ∨' (x [ =' ] (((+ 2) *' y) +' (num' (+ 1)))))
    where
      x = var' (suc zero)
      y = var' zero
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Decision procedures}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

There exist numerous procedures able to decide Presburger
arithmetic. They are primarily distinguished by the domain of their
formulas. The validity of these Presburger formulas gets carried onto
superset domains; the non-validity gets carried onto subset domains.

\todo{Cite}
\cite{Janicic1997a}

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

Some Presburger formulas are valid on integers but invalid on natural
numbers: $∃x.\:x+1=0$. Others are valid on rational numbers but
invalid on integers: $∃x.\:2x=1$. \todo{cite intro} When considering
which decision procedures to explore, we immediately discarted the
ones acting on real numbers — irrational numbers are not
straightforward to handle in constructive mathematics. The most
well-documented procedures are on integers, and the usage of integer
Presburger arithmetic is common enough for an automated solver to be
of value. To solve a problem on natural numbers, we just need add a
condition $0 ≤ x$ to every existential quantifier.

We have choosen the Omega Test and Cooper's Algorithm as two decision
procedures on integers of interest to explore. Michael Norrish depicts
in \cite{Norrish2003} the state of affairs of the implementation of
Presburger arithmetic deciding procedures by proof assistants. He then
continues describing the Omega Test and Cooper's Algorithm and
proposes implementations for both of them for the proof assistant
HOL. Our attempt to implement both procedures in Agda is significantly
based on his work, which he also briefly outlines in a later
talk. \cite{Norrish2006}

\subsubsection{Common ideas}

Both algorithms have certain aspects in common. As part of their
normalisation process, they require the elimination of universal
quantifiers. This is carried out resorting to the following
equivalence:

\begin{equation*}
∀x.\:P(x) \equiv ¬∃x.\:¬P(x)
\end{equation*}

Existential quantifiers are distributed over disjunctions:

\begin{equation*}
∃x.\:P(x) \lor Q(x) \equiv (∃x.\:P(x)) \lor (∃x.\:Q(x))
\end{equation*}

Negation needs to be pushed inside conjunctions and disjunctions and
double negation eliminated:

\begin{align*}
\neg (P(x) \land Q(x)) &\equiv \neg P(x) \lor  \neg Q(x) \\
\neg (P(x) \lor  Q(x)) &\equiv \neg P(x) \land \neg Q(x) \\
\neg \neg P(x)         &\equiv P(x) 
\end{align*}

By limiting their domain to the integers, they can both translate all
relations on ~\AgdaDatatype{Atom}s into a canonical form: $0 ≤ ax + by
+ \ldots + cz + k$. Operations on ~\AgdaDatatype{Atom}s can be
evaluated into linear transformations of the form $ax + by + \ldots +
cz + k$. We use a single type to represent both and keep record of the
number of variables in the linear inequation, so that we can push this
requirement onto the vector of coefficients. Here, each coefficient's
index indicates the distance to where that variable was introduced.

\begin{code}
  record Linear (i : ℕ) : Set where
    constructor _∷+_
    field
      cs : Vec ℤ i
      k : ℤ
\end{code}

\AgdaHide{
\begin{code}
  open Linear
  pattern _x+_+ℤ_ c cs k = (c ∷ cs) ∷+ k
  
  infixl 20 _⊕_
  infixl 20 _⊝_

  #_ : ∀ {i} → ℤ → Linear i
  # k = Vec.replicate (+ 0) ∷+ k
  
  ø : ∀ {i} → Linear i
  ø = Vec.replicate (+ 0) ∷+ (+ 0)
  
  _x+∅ : ∀ {i} → ℤ → Linear (suc i)
  n x+∅ = (n ∷ Vec.replicate (+ 0)) ∷+ (+ 0)
  
  _x+_ : ∀ {i} → ℤ → Linear i → Linear (suc i)
  n x+ (cs ∷+ k) = (n ∷ cs) ∷+ k

  _≤_x : ∀ {i} → Linear i → ℤ → Linear (suc i)
  (cs ∷+ k) ≤ α x = (α ∷ (Vec.map -_ cs)) ∷+ (- k)

  _x≤_ : ∀ {i} → ℤ → Linear i → Linear (suc i)
  β x≤ (cs ∷+ k) = ((- β) ∷ cs) ∷+ k
  
  ⇑1 : ∀ {i} → Linear i → Linear (suc i)
  ⇑1 (cs ∷+ k) = ((+ 0) ∷ cs) ∷+ k
  
  _⊛_ : ∀ {i} → ℤ → Linear i → Linear i
  z ⊛ (cs ∷+ k) = Vec.map (z *_) cs ∷+ (z * k)
 
  _⊕_ : ∀ {i} → Linear i → Linear i → Linear i
  (cs₁ ∷+ k₁) ⊕ (cs₂ ∷+ k₂) = Vec.zipWith _+_ cs₁ cs₂ ∷+ (k₁ + k₂)
 
  ⊝_ : ∀ {i} → Linear i → Linear i
  ⊝ (cs ∷+ k) = (Vec.map -_ cs) ∷+ (- k)

  _⊝_ : ∀ {i} → Linear i → Linear i → Linear i
  a ⊝ b = a ⊕ (⊝ b)

  ⊘ : ∀ {i} → Linear i → Linear i
  ⊘ a = (# (+ 1)) ⊝ a
  
  head : ∀ {i} → Linear (suc i) → ℤ
  head (c x+ cs +ℤ k) = c

  tail : ∀ {i} → Linear (suc i) → Linear i
  tail (c x+ cs +ℤ k) = cs ∷+ k
  
  substitute : ∀ {i} → Linear i → Linear (suc i) → Linear i
  substitute x a = (head a ⊛ x) ⊕ tail a

  irrelevant : ∀ {i} → Linear (suc i) → Set
  irrelevant a = + 0 ≡ head a

  lower-bound : ∀ {i} → Linear (suc i) → Set
  lower-bound a = + 0 < head a

  upper-bound : ∀ {i} → Linear (suc i) → Set
  upper-bound a = + 0 > head a

  classifyₐ : ∀ {i} → (a : Linear (suc i)) → Tri (lower-bound a) (irrelevant a) (upper-bound a)
  classifyₐ = <-cmp (+ 0) ∘ head 
      
  classify : ∀ {i} → (as : List (Linear (suc i)))
             → (List (Σ (Linear (suc i)) lower-bound))
             × (List (Σ (Linear (suc i)) irrelevant))
             × (List (Σ (Linear (suc i)) upper-bound))
  classify [] = [] , [] , []
  classify (a ∷ as) with classifyₐ a | classify as
  classify (a ∷ as) | Tri.tri< p _ _ | ls , is , us = (a , p) ∷ ls , is , us
  classify (a ∷ as) | Tri.tri≈ _ p _ | ls , is , us = ls , (a , p) ∷ is , us
  classify (a ∷ as) | Tri.tri> _ _ p | ls , is , us = ls , is , (a , p) ∷ us
\end{code}
}

Relations can then be normalised as follows:

\begin{align*}
p < q &\equiv 0 ≤ q - p + 1 \\
p > q &\equiv 0 ≤ p - q + 1 \\
p ≤ q &\equiv 0 ≤ q - p     \\
p ≥ q &\equiv 0 ≤ p - q     \\
p = q &\equiv 0 ≤ q - p \land 0 ≤ p - q
\end{align*}
  
As part of their existential quantifier elimination step, both
algorithms require to have variable coefficients set to $1$ or
$-1$. First, the lowest common multiplier $ℓ$ of all coefficients on
$x$ is computed, then all atoms are multiplied appropriately so that
their coefficient on $x$ becomes equal to the LCM $ℓ$. Finally, all
coefficients are divided by $ℓ$ in accordance to the following
equivalence:

\begin{equation*}
P(ℓx) \equiv P(x) \land ℓ | x
\end{equation*}

Divide terms are a special case where a natural number and an
\AgdaDatatype{Atom} are related. The Omega Test and Cooper's Algorithm
handle divide terms differently, and we will therefore analyse their
use separately. It suffices to say that divide terms and their
negations can be eliminated by introducing existential quantifiers,
which is often not desirable.

\begin{align*}
n ∣ a &\equiv ∃x.\:nx = a \\
n ∤ a &\equiv ∃x.\:\bigvee_{i ∈ 1 \ldots n - 1} nx = (a + i)
\end{align*}

Finally, the heart of both decision procedures are equivalence
theorems that eliminate a single innermost existential quantifier. Let
~\AgdaDatatype{NormalForm}~\AgdaBound{i}~ represent a normal form
containing no quantifiers and where ~\AgdaBound{i}~ variables are
available. Then both decision procedures will return an equivalent
form with the variable referring to the most recent binding
eliminated:

\begin{code}
  Elimination : (ℕ → Set) → ℕ → Set
  Elimination NormalForm i = NormalForm (suc i) → NormalForm i
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{The Omega Test}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

The Omega Test was first introduced as a Presburger arithmetic
deciding procedure in \cite{Pugh1991}. It adapts Fourier-Motzkin
elimination — which acts on real numbers — to integers.

\subsubsection{Normalisation}

The Omega Test requires input formulas to be put into disjunctive
normal form. This makes normalisation an expensive exponential
step, as can be seen when cojunctions are normalised over
disjunctions:

\begin{equation*}
(P \lor Q) \land (R \lor S) \equiv (P \land R) \lor (P \land S) \lor
(Q \land R) \lor (Q \land S)
\end{equation*}

The result of normalisation has to be a structure where:

\begin{itemize}[noitemsep]
  \item the upper layer is a disjunction;
  \item a disjunction only contains conjunctions;
  \item a conjunction only contains conjunctions, existential
        quantifiers, negated existential quantifiers, or
        ~\AgdaDatatype{Linear}s;
\end{itemize}

The following tree structure discerns, inside of each conjunction,
those substructures that contain existentials from those that do
not. This helps identify conjunctions on which the elimination step
can be performed — those with ~\AgdaField{existentials}~ empty. An
alternative is to expand the list ~\AgdaField{existentials}~ into two
lists: one containing conjunctions inside existentials, the other
containing conjunctions inside negated existentials. The proposed
implementation makes it easier to handle both
~\AgdaInductiveConstructor{∃}~ and ~\AgdaInductiveConstructor{¬∃}~
uniformly.

As with ~\AgdaDatatype{Formula}s, note that the information about the
number of available variables is pushed inside the structure —
~\AgdaDatatype{DNF}~\AgdaBound{n} can only contain
~\AgdaDatatype{Conjunction}~\AgdaBound{n}~ and so forth. The
constructors ~\AgdaInductiveConstructor{∃}~ and
\AgdaInductiveConstructor{¬∃} make one variable more available.

\begin{code}
  mutual
    data Existential (i : ℕ) : Set where
      ¬∃ : Conjunction (suc i) → Existential i
      ∃  : Conjunction (suc i) → Existential i
  
    record Conjunction (i : ℕ) : Set where
      inductive
      constructor 0≤_∧_E
      field
        constraints : List (Linear i)
        existentials : List (Existential i)
  
  DNF : (i : ℕ) → Set
  DNF i = List (Conjunction i)
\end{code}

Normalisation proceeds recursively, eliminating universal quantifiers,
pushing conjunction and negation inward, normalising implication,
evaluating operations on atoms and normalising relations between them.

\todo{Add anex}
\AgdaHide{
\begin{code}
  open Existential public
  open Conjunction public
  
  ¬-existential : ∀ {i} → Existential i → Existential i
  ¬-existential (¬∃ x) = ∃ x
  ¬-existential (∃ x) = ¬∃ x
    
  ¬-conjunction : ∀ {i} → Conjunction i → DNF i
  ¬-conjunction 0≤ cs ∧ bs E = List.map (λ c → 0≤ ⊘ c ∷ [] ∧                   [] E) cs
                            ++ List.map (λ b → 0≤       [] ∧ ¬-existential b ∷ [] E) bs
                                                                                               
  _∧-dnf_ : ∀ {i} → DNF i → DNF i → DNF i
  xs ∧-dnf ys = List.map 
     (λ {((0≤ cx ∧ bx E) , (0≤ cy ∧ by E)) → 0≤ cx ++ cy ∧ bx ++ by E})
     (×-list xs ys)
  
  _∨-dnf_ : ∀ {i} → DNF i → DNF i → DNF i
  _∨-dnf_ = _++_
  
  ¬-dnf_ : ∀ {i} → DNF i → DNF i
  ¬-dnf_ = List.foldl (λ dnf conj → dnf ∧-dnf ¬-conjunction conj) []
  
  _⇒-dnf_ : ∀ {i} → DNF i → DNF i → DNF i
  xs ⇒-dnf ys = (¬-dnf xs) ∨-dnf (xs ∧-dnf ys)
  
  ∃-dnf_ : ∀ {i} → DNF (suc i) → DNF i
  ∃-dnf_ = List.map λ conj → 0≤ [] ∧ (∃ conj ∷ []) E
                                                     
  ∀-dnf : ∀ {i} → DNF (suc i) → DNF i
  ∀-dnf = ¬-dnf_ ∘ ∃-dnf_ ∘ ¬-dnf_
  
  norm-rel : ∀ {i} → Rel → Linear i → Linear i → List (Linear i)
  norm-rel <' l₁ l₂ = (l₂ ⊝ l₁) ⊕ (# (+ 1)) ∷ []
  norm-rel >' l₁ l₂ = (l₁ ⊝ l₂) ⊕ (# (+ 1)) ∷ []
  norm-rel ≤' l₁ l₂ = l₂ ⊝ l₁ ∷ []
  norm-rel ≥' l₁ l₂ = l₁ ⊝ l₂ ∷ []
  norm-rel =' l₁ l₂ = l₂ ⊝ l₁ ∷ l₁ ⊝ l₂ ∷ []

  norm-atom : ∀ {i} → Atom i → Linear i
  norm-atom (num' n) = # n
  norm-atom (x +' y) = (norm-atom x) ⊕ (norm-atom y)
  norm-atom (n *' x) = n ⊛ (norm-atom x)
  norm-atom (var' zero) = (+ 1) x+∅
  norm-atom (var' (suc n)) with norm-atom (var' n)
  ...                     | cs ∷+ k = (+ 0) x+ cs +ℤ k
    
  norm-form : {i : ℕ} → Formula i → DNF i
  norm-form (x ∧' y) = (norm-form x) ∧-dnf (norm-form y)
  norm-form (x ∨' y) = (norm-form x) ∨-dnf (norm-form y)
  norm-form (x ⇒' y) = (norm-form x) ⇒-dnf (norm-form y)
  norm-form (¬' x) = ¬-dnf (norm-form x)
  norm-form (∃' x) = ∃-dnf (norm-form x)
  norm-form (∀' x) = ∀-dnf (norm-form x)
  norm-form (d ∣' x) = 0≤ {!!} ∧ [] E ∷ []
  norm-form (x [ r ] y) = 0≤ norm-rel r (norm-atom x) (norm-atom y) ∧ [] E ∷ []
\end{code}
}


\subsubsection{Elimination}

\subsubsection{Verification}

\todo{Many things:}
Main theorem, what it acts upon
Explain how divides terms created by splinters need to be handled
Why we don't handle divide terms
Why just dark-shadow
What solving the dark-shadow implies
What the proof looks like
Mention splitting linears into three cats
Mention why it is easier to handle irrelevant linears like this


Pugh's main theorem acts on conjuntions with the following form:

\begin{code}
  dark-shadow : ∀ {i} → Linear (suc i) → Linear (suc i) → Linear i
  dark-shadow l u with head l | ⊝ (tail l) | - (head u) | tail u
  ...             | α | a | β | b = (α ⊛ b) ⊝ (β ⊛ a) ⊝ (# ((α - + 1) * (β - + 1)))
      
  omega : ∀ {i} → List (Linear (suc i)) → List (Linear i)
  omega as with classify as
  omega as | ls , is , us = List.map (λ { ((l , _) , (u , _)) → dark-shadow l u}) (×-list ls us)
                         ++ List.map (tail ∘ proj₁) is

  Env : ℕ → Set
  Env i = Vec ℤ i

  _[_/x]ₗ : ∀ {i} → Linear i → Env i → Linear 0
  a [ [] /x]ₗ = a
  a [ (x ∷ xs) /x]ₗ = (substitute (# x) a) [ xs /x]ₗ
  
  _[_/x] : ∀ {i} → List (Linear i) → Env i → List (Linear 0)
  as [ xs /x] = List.map _[ xs /x]ₗ as

  ⊨ₗ₀ : Linear 0 → Set
  ⊨ₗ₀ a = (+ 0) < (Linear.k a)

  ⊨₀ : List (Linear 0) → Set
  ⊨₀ = All ⊨ₗ₀

  ⊨ₗ : ∀ {i} → Linear i → Set
  ⊨ₗ {i} a = Σ (Env i) λ ρ → ⊨ₗ₀ (a [ ρ /x]ₗ)

  ⊨ : ∀ {i} → List (Linear i) → Set
  ⊨ {i} as = Σ (Env i) λ ρ → ⊨₀ (as [ ρ /x])

  ⊭ : ∀ {i} → List (Linear i) → Set
  ⊭ {i} as = (ρ : Env i) → ⊨₀ (as [ ρ /x]) → ⊥
  
  ¬⊭→⊨ : (as : List (Linear 0)) → (⊭ as → ⊥) → ⊨ as
  ¬⊭→⊨ = {!!}
  
  
  ⟦_⟧ₗ₀ : (a : Linear 0) → Dec (⊨ₗ₀ a)
  ⟦ a ⟧ₗ₀ = (+ 0) <? (Linear.k a)

  ⟦_⟧₀ : (as : List (Linear 0)) → Dec (⊨₀ as)
  ⟦ [] ⟧₀ = yes []
  ⟦ a ∷ as ⟧₀ with ⟦ a ⟧ₗ₀ | ⟦ as ⟧₀
  ⟦ a ∷ as ⟧₀ | no ¬pa | _       = no λ { (pa ∷ pas) → ¬pa pa}
  ⟦ a ∷ as ⟧₀ | yes _  | no ¬pas = no λ { (_ ∷ pas) → ¬pas pas}
  ⟦ a ∷ as ⟧₀ | yes pa | yes pas = yes (pa ∷ pas)

  ⟦_⟧ : ∀ {i} → (as : List (Linear i)) → (xs : Env i) → Dec (⊨₀ (as [ xs /x]))
  ⟦ as ⟧ xs = ⟦ as [ xs /x] ⟧₀

  ⟦_⟧Ω : ∀ {i} → List (Linear i) → Bool
  ⟦_⟧Ω {zero} a with ⟦ a ⟧₀
  ...           | yes p = true
  ...           | no ¬p = false
  ⟦_⟧Ω {suc i} a = ⟦ omega a ⟧Ω
  
  
  module Ω-Inner (i : ℕ) (l u : Linear (suc i)) (lbl : lower-bound l) (ubu : upper-bound u) where
    α = head l
    a = ⊝ (tail l)
    0<α : (+ 0) < α
    0<α = {!!}
    β = - (head u)
    b = tail u
    0<β : (+ 0) < β
    0<β = {!!}
    
    [α-1][β-1]≤αb-aβ : Linear i
    [α-1][β-1]≤αb-aβ = (α ⊛ b) ⊝ (β ⊛ a) ⊝ (# ((α - + 1) * (β - + 1)))
    
    aβ≤αb : Linear i
    aβ≤αb = ((α ⊛ b) ⊝ (β ⊛ a))

    aβ≤αβx≤αb : List (Linear (suc i))
    aβ≤αβx≤αb = ((α * β) x+∅) ⊝ (β ⊛ ⇑1 a)
              ∷ (α ⊛ ⇑1 b) ⊝ ((α * β) x+∅)
              ∷ []

    αβn<aβ≤αb<αβ[n+1] : ℕ → List (Linear i)
    αβn<aβ≤αb<αβ[n+1] n = ((β ⊛ a) ⊝ (# (α * β * + n)) ⊝ (# (+ 1)))
                        ∷ (α ⊛ b) ⊝ (β ⊛ a)
                        ∷ ((# (α * β * + (suc n))) ⊝ (α ⊛ b) ⊝ (# (+ 1)))
                        ∷ []
  
    α≤αβ[n+1]-αb : ℕ → Linear i
    α≤αβ[n+1]-αb n = (# (α * β * + (suc n))) ⊝ (α ⊛ b) ⊝ (# α)

    β≤aβ-αβn : ℕ → Linear i
    β≤aβ-αβn n = (β ⊛ a) ⊝ (# (α * β * + n)) ⊝ (# β)

    αb-aβ<[α-1][β-1] : Linear i
    αb-aβ<[α-1][β-1] = (# ((α - + 1) * (β - + 1))) ⊝ (α ⊛ b) ⊝ (β ⊛ a) ⊝ (# (+ 1))

    ⊨βa≤αb : ⊨ₗ (dark-shadow l u) → ⊨ₗ aβ≤αb
    ⊨βa≤αb (ρ , pds) = ρ , bar ((α ⊛ b) ⊝ (β ⊛ a)) ((α - + 1) * (β - + 1)) {!!} ρ pds 
      where
        open IntProp.≤-Reasoning
        open import Data.Vec.Properties using (map-id ; map-cong ; zipWith-replicate₂)
        open import Data.Integer.Properties using (+-identityʳ ; ≤-reflexive)

        foo : (m : ℤ) (n : ℕ) → m - + n Int.≤ m
        foo m zero = ≤-reflexive (+-identityʳ m)
        foo m (suc n) = begin 
          m + - + suc n
            ≤⟨ {!!} ⟩
          m
            ∎
        
        bar : ∀ {i} → (a : Linear i) (n : ℤ) (pn : (+ 0) Int.≤ n) (ρ : Env i) → ⊨ₗ₀ (a ⊝ (# n) [ ρ /x]ₗ) → ⊨ₗ₀ (a [ ρ /x]ₗ)
        bar (csa ∷+ ka) n pn ρ p = begin 
          + 1
            ≤⟨ p ⟩
          k (((csa ∷+ ka) ⊝ (# n)) [ ρ /x]ₗ)
            ≡⟨ refl ⟩
          k ((Vec.zipWith _+_ csa (Vec.map -_ (Vec.replicate (+ 0))) ∷+ (ka + - n)) [ ρ /x]ₗ)
            ≡⟨ {!!} ⟩
          {!!}
            ≡⟨ {!!} ⟩
          k ((csa ∷+ (ka + - n)) [ ρ /x]ₗ)
            ≤⟨ {!!} ⟩
          k ((csa ∷+ ka) [ ρ /x]ₗ)
            ∎
        
    ⊨αβn<aβ≤αb<αβ[n+1] : ⊨ₗ aβ≤αb → ⊭ (l ∷ u ∷ []) → Σ ℕ λ n → ⊨ (αβn<aβ≤αb<αβ[n+1] n)
    ⊨αβn<aβ≤αb<αβ[n+1] (ρ , ⊨p₁) ⊭p₂ = n , ρ , r₁ ∷ r₂ ∷ r₃ ∷ []
      where
        -- How to compute n?
        open IntProp.≤-Reasoning
        n = {!!}
        ⊭aβ≤αβx≤αb : ⊭ ((α * β) x+∅ ⊝ ⇑1 (β ⊛ a) ∷ ⇑1 (α ⊛ b) ⊝ ((α * β) x+∅) ∷ [])
        ⊭aβ≤αβx≤αb ρ' (⊨p₃ ∷ ⊨p₄ ∷ []) = ⊭p₂ ρ' ({!!} ∷ {!!} ∷ [])
        
        r₁ = begin
          + 1
            ≤⟨ {!!} ⟩
          k (((β ⊛ a) ⊝ (# (α * β * + n)) ⊝ (# (+ 1))) [ ρ /x]ₗ)
            ∎
        r₂ = begin
          + 1
            ≤⟨ {!!} ⟩
          k (((α ⊛ b) ⊝ (β ⊛ a)) [ ρ /x]ₗ)
            ∎
        r₃ = begin
          + 1
            ≤⟨ {!!} ⟩
          k (((# (α * β * + suc n)) ⊝ (α ⊛ b) ⊝ (# (+ 1))) [ ρ /x]ₗ)
            ∎
    
    ⊨α≤αβ[n+1]-αb : (n : ℕ) →  ⊨ (αβn<aβ≤αb<αβ[n+1] n) → ⊨ₗ (α≤αβ[n+1]-αb n)
    ⊨α≤αβ[n+1]-αb n (ρ , (⊨p₁ ∷ ⊨p₂ ∷ ⊨p₃ ∷ [])) = ρ , (begin 
      + 1
        ≤⟨ {!!} ⟩
      k (α≤αβ[n+1]-αb n [ ρ /x]ₗ)
        ∎)
      where open IntProp.≤-Reasoning
    
    ⊨β≤aβ-αβn : (n : ℕ) →  ⊨ (αβn<aβ≤αb<αβ[n+1] n) → ⊨ₗ (β≤aβ-αβn n)
    ⊨β≤aβ-αβn n (ρ , (⊨p₁ ∷ ⊨p₂ ∷ ⊨p₃ ∷ [])) = ρ , (begin 
      + 1
        ≤⟨ {!!} ⟩
      k (β≤aβ-αβn n [ ρ /x]ₗ)
        ∎)
      where open IntProp.≤-Reasoning

    ⊨αb-aβ<[α-1][β-1] : {n : ℕ} → ⊨ (α≤αβ[n+1]-αb n ∷ β≤aβ-αβn n ∷ []) → ⊨ₗ αb-aβ<[α-1][β-1]
    ⊨αb-aβ<[α-1][β-1] (ρ , (⊨p₁ ∷ ⊨p₂ ∷ [])) = ρ , (begin 
      + 1
        ≤⟨ {!!} ⟩
      k (αb-aβ<[α-1][β-1] [ ρ /x]ₗ)
        ∎)
      where open IntProp.≤-Reasoning

    ⊨⊥ : ⊨ ([α-1][β-1]≤αb-aβ ∷ αb-aβ<[α-1][β-1] ∷ []) → ⊥
    ⊨⊥ (ρ , (⊨p ∷ ⊭p ∷ [])) = {!!}

  Ω-Correct : ∀ {i} (as : List (Linear i)) → Set
  Ω-Correct as with ⟦ as ⟧Ω
  Ω-Correct as | false = ⊤
  Ω-Correct as | true  = ⊨ as

  Ω-correct : ∀ {i} (p : List (Linear (suc i))) → Ω-Correct p
  Ω-correct p with true ≡ ⟦ p ⟧Ω | ⟦ p ⟧Ω
  Ω-correct p | z | false = tt
  Ω-correct p | z | true = {!!}
    where
    inner : T ⟦ p ⟧Ω → ⊨ p
    inner ep = {!!} 

            
\end{code}


Divides term elimination procedure

\begin{align*}
    ∃x . (d₁ ∣ a₁x + e₁) ∧ (d₂ ∣ a₂x + e₂) ∧ (a₃x + e₃)
    \intertext{Introduce existential for first term}
    ∃x . ∃y . (d₁y = a₁x + e₁) ∧ (d₂ ∣ a₂x + e₂) ∧ (a₃x + e₃)
    \intertext{Rearrange first term}
    ∃x . ∃y . (a₁x = d₁y - e₁) ∧ (d₂ ∣ a₂x + e₂) ∧ (a₃x + e₃)
    \intertext{Multiply all outer coefficients to a common LCM}
    ∃x . ∃y . (mx = n₁d₁y - n₁e₁) ∧ (n₂d₂ ∣ mx + n₂e₂) ∧ (mx + n₃e₃)
    \intertext{Substitute mx}
    ∃y . (m ∣ n₁d₁y - n₁e₁) ∧ (n₂d₂ ∣ n₁d₁y - n₁e₁ + n₂e₂) ∧ (n₁d₁y - n₁e₁ + n₃e₃)
\end{align*}

Because $m < d₁$, this will eventually end. It might get
shortcircuited if $d₁ ∣ a₁$ and $d₁ ∣ e₁$.

\todo{How does it work with multiple divide terms?}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Cooper's Algorithm}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\cite{Cooper1972}
\cite{Chaieb2003}

\AgdaHide{
\begin{code}
    
  -- module Constraint where
  --   data Constraint (i : ℕ) : Set where
  --     0<_ :           (e : Linear i) → Constraint i
  --     _∣_ : (d : ℕ) → (e : Linear i) → Constraint i
  --     _∤_ : (d : ℕ) → (e : Linear i) → Constraint i
  --   
  --   affine : ∀ {i} → Constraint i → Linear i
  --   affine (0< e)  = e
  --   affine (d ∣ e) = e
  --   affine (d ∤ e) = e
  --   
  --   on-affine : ∀ {i j} (f : Linear i → Linear j) → (Constraint i → Constraint j)
  --   on-affine f (0< e)  = 0< f e
  --   on-affine f (d ∣ e) = d ∣ f e
  --   on-affine f (d ∤ e) = d ∤ f e
  --   
  --   on-coefficient : ∀ {i} → (ℤ → ℤ) → (Linear (suc i) → Linear (suc i))
  --   on-coefficient f ((c ∷ cs) ∷+ k) = ((f c) ∷ cs) ∷+ k
  --   
  --   coefficient : ∀ {i} → Constraint (suc i) → ℤ
  --   coefficient = Aff.head ∘ affine

  --   divisor : ∀ {i} → Constraint i → Maybe ℕ
  --   divisor (0< e)  = nothing
  --   divisor (d ∣ e) = just d
  --   divisor (d ∤ e) = just d
  -- 
  --   ¬_ : ∀ {i} → Constraint i → Constraint i
  --   ¬ (0< e) = 0< (Aff.¬ e)
  --   ¬ (d ∣ e) = d ∤ e
  --   ¬ (d ∤ e) = d ∣ e
  --   
  -- open Constraint using (Constraint ; 0<_ ; _∣_ ; _∤_)
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Future work}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Omega:
  Evaluation
  Splinters
  Adapt stdlib

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Verification and validation}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\todo{Dependent types, higher standards, no tests, we formally describe what correct is}
\todo{This report is type-checked}

%   Verification and Validation In this section you should outline the
%   verification and validation procedures that you've adopted throughout the
%   project to ensure that the final product satisfies its specification. In
%   particular, you should outline the test procedures that you adopted during
%   and after implementation. Your aim here is to convince the reader that the
%   product has been thoroughly and appropriately verified. Detailed test
%   results should, however, form a separate appendix at the end of the report.

- Why is this absolutely correct, Agda?

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Results and evaluation}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \chapter{Related work}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%   Related Work You should survey and critically evaluate other work which you
%   have read or otherwise considered in the general area of the project topic.
%   The aim here is to place your project work in the context of the related
%   work.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Summary and conclusions}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
