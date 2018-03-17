\documentclass[12pt,a4paper]{scrreprt}

\usepackage[english]{babel}

% Equations
\usepackage{amsmath}

% Theorems
\usepackage{amsthm}
\newtheorem{theorem}{Theorem}

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

% Inline lists
\usepackage[inline]{enumitem}

% Appendices
\usepackage[toc,page]{appendix}
\renewcommand{\appendixname}{Appendix}
\renewcommand{\appendixtocname}{Appendix}
\renewcommand{\appendixpagename}{Appendix}

% Include parts of other files
\usepackage{catchfilebetweentags}

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

\todo{Special mention to my neighbour's dog}
\todo{Dysphoria}

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
\url{https://agda.readthedocs.io}. This section will briefly cover the
basics of what theorem proving in Agda looks like and, in the spirit
of a tutorial, it will sometimes use the second person to avoid 
excessive third person references like ``the user'' and ``the
programmer''.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{The experience of programming in Agda}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Development in Agda happens inside Emacs, and is a two way
conversation between the compiler and the programmer. Wherever a
definition is required, you may instead write $?$ and request the
type-checker to reload the file. A ``hole'' will appear where the $?$
was. You can then:

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
driven'', allows you to work with partial definitions and receive
constant feedback from the type-checker.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Some peculiarities}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

If an argument is named, subsequent arguments can depend on it.  If an
argument can be inferred by the type-checker, you may choose to make
it implicit by naming it and enclosing it in curly braces. Implicit
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

Whenever you pattern match against a datatype, it will split into
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
pattern matching on it will render the case absurd, and thus you won't
need to provide a definition for it.

\begin{code}
    -- The successor of an even number cannot be even
    prf₂ : ∀ n → {p : Even n} → Even (suc n) → ⊥
    prf₂ zero {p} ()
    prf₂ (suc zero) {()} sp
    prf₂ (suc (suc n)) {p} sp = prf₂ n {p} sp 
\end{code}

The type-checker uses dot patterns to show that pattern matching on
one argument uniquely implies another. If a value can be inferred by
the type checker, you may replace it by an underscore. Additionally,
underscores can be used as non-binded catch-alls outside of dot
patterns on the left hand side of a definition.

\begin{code}
    -- Pattern matching on xs determines n
    zipWith' : {A B C : Set} (n : ℕ) (f : A → B → C) → Vec A n → Vec B n → Vec C n
    zipWith' .zero f [] [] = []
    zipWith' .(suc _) f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith' _ f xs ys
\end{code}

``With abstraction'' gives you the ability to steer unification in a
particular direction by allowing you to pattern match on arbitrary
well-formed expressions on the left hand side of a definition. This
may result in the refinement of the rest of the arguments. The
following example is adapted from Agda-Stdlib and was originally
presented in \cite{McBride2004}:

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
\AgdaBound{m} and \AgdaBound{n}. This is the difference between with
abstraction and ordinary case splitting on the right hand
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

You can now leave a record of type rewrites and their justifications:

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

\ExecuteMetaData[Monoids.tex]{monoid}

\AgdaRef{M}, the set on which the monoid is defined, is often referred
to as the carrier. $(ℕ, +, 0)$ and $(ℕ, ·, 1)$ are both examples of
monoids. Note however that these also happen to be commutative, while
monoids need not be — more on solving commutative monoids later. An
example of a non-commutative monoid are lists together with the
concatenation operation:

\ExecuteMetaData[Monoids.tex]{list-monoid}

An equation on monoids cannot be decided by unification alone: the
monoid laws show that definitionally distinct propositions might in
fact have the same meaning.

\ExecuteMetaData[Monoids.tex]{eqn1}

Without an automated solver, the number of law applications and hence
the length of the proof grows linearly with respect to the size of the
monoid. An automated solver should allow us to effortlessly satisfy a
proposition like the following:

\ExecuteMetaData[Monoids.tex]{eqn2}

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

\ExecuteMetaData[Monoids.tex]{expr}

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

\ExecuteMetaData[Monoids.tex]{normal-form}

The normalising function ignores neutral elements and preserves order:

\ExecuteMetaData[Monoids.tex]{normalise}

From here on, we will work with a concrete monoid (\AgdaBound{monoid})
on a concrete carrier \AgdaBound{M}. This results in all of the
definitions inside of the module having \AgdaBound{M} and
\AgdaBound{monoid} defined. When called from the outside of this
module, these definitions will have
\AgdaSymbol{\{}\AgdaBound{M}~\AgdaSymbol{:}~\AgdaPrimitiveType{Set}\AgdaSymbol{\}}~\AgdaSymbol{(}\AgdaBound{monoid}~\AgdaSymbol{:}~\AgdaRecord{Monoid}~\AgdaBound{M}\AgdaSymbol{)}
prepended to their type. We can also make the insides of
\AgdaBound{monoid} directly accessible by opening it as if it were a
module.

\ExecuteMetaData[Monoids.tex]{monoid-module}

To evaluate an expression we need a concrete assignment for the
variables contained within. We call this an environment. An
environment is a lookup table where each of the indices has an
associated value in the carrier \AgdaBound{M}.
The size of \AgdaDatatype{Fin}~\AgdaBound{n} is equal to the size
of \AgdaDatatype{Vec}~\AgdaBound{M}~\AgdaBound{n}, and so we can
define a bijection between \AgdaDatatype{Fin}~\AgdaBound{n}
and \AgdaDatatype{Vec}~\AgdaBound{M}~\AgdaBound{n}.

\ExecuteMetaData[Monoids.tex]{env}

Once we have expressions, normal forms end environments, we can define
what the evaluation of both — expressions and normal forms — is. Note
that both definitions rule out expressions and normal forms with more
indices than the environment contains — every index within the
expression has to have a corresponding value in the environment.

\ExecuteMetaData[Monoids.tex]{evaluation}

We are finally ready to make our claim: an equation on monoids holds
provided that both sides of the equation match after
normalisation. We cannot make any claims in the other direction — if
both sides do not equal after normalisation the equation must be
false. This can most clearly be seen by taking the unit type (the type
with a single value) as carrier of the monoid: all equations are true,
yet the monoid laws allow to prove only some of them. Because we
cannot make any interesting claims, we can claim true the trivial.

\ExecuteMetaData[Monoids.tex]{solution}

We define decidable equality of normal forms (here \AgdaRef{\_≟\_})
by relying on the definitions of decidable equality of lists and
finite indices.

\AgdaRef{Solution}~ returns an appropriate per-equation specification
for every ~\AgdaDatatype{Eqn}~\AgdaBound{n}. We must now prove that we
are able to meet such specifications.

\ExecuteMetaData[Monoids.tex]{solve-type}

The crux of such a proof is to show that the evaluation of an
expression can be decomposed into the normalisation into a normal form
and its posterior evaluation.

\ExecuteMetaData[Monoids.tex]{eval-commutes-type}

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

\ExecuteMetaData[Monoids.tex]{solve}

Showing \AgdaRef{eval-commutes} is done inductively and it requires a
proof that concatenation of normal forms (\AgdaRef{\_++\_}) preserves
the structure of monoids. Note that these proofs, perhaps
unsurprisingly, use all of the monoid laws.

\ExecuteMetaData[Monoids.tex]{eval-commutes}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Results and usage}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

We can now automatically generate proofs for arbitrary equations on monoids:

\ExecuteMetaData[Monoids.tex]{eqn1-auto}

However, we still need to manually build the expressions representing
the target theorem. This includes handling the indices referring to
variables appropriatly. As shown by \cite{Bove2009} at
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

From here on, we will assume the following syntax for Presburger
predicates:

\ExecuteMetaData[Presburger.tex]{formula}

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

\ExecuteMetaData[Presburger.tex]{pred}

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

The heart of both decision procedures are equivalence theorems that
eliminate a single innermost existential quantifier. Let $P$ and $Q$
be quantifier-free formulas, then both theorems are of form:

\begin{equation*}
∃x.\:P(x) \equiv Q
\end{equation*}

This elimination process has to be ran recursively from the bottom
up. The result, a formula with no variables, can then be trivially
evaluated. 

By limiting their domain to the integers, they can both translate all
relations on ~\AgdaDatatype{Atom}s into a canonical form: $0 ≤ ax + by
+ \ldots + cz + k$. Operations on ~\AgdaDatatype{Atom}s can be
evaluated into linear transformations of the form $ax + by + \ldots +
cz + k$. We use a single type to represent both and keep record of the
number of variables in the linear inequation, so that we can push this
requirement onto the vector of coefficients. Here, each coefficient's
index indicates the distance to where that variable was introduced.
The goal of any decision procedure is thus to return an equivalent
structure containing only ~\AgdaDatatype{Linear}~\AgdaNumber{0}.

\ExecuteMetaData[Presburger.tex]{linear}

Universal quantifiers need to be eliminated as part of their
normalisation process. This is carried out resorting to the following
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

Relations can then be normalised as follows:

\begin{align*}
p < q &\equiv 0 ≤ q - p + 1 \\
p > q &\equiv 0 ≤ p - q + 1 \\
p ≤ q &\equiv 0 ≤ q - p     \\
p ≥ q &\equiv 0 ≤ p - q     \\
p = q &\equiv 0 ≤ q - p \land 0 ≤ p - q
\end{align*}
  
Divide terms are a special case where a natural number and an
\AgdaDatatype{Atom} are related. The Omega Test and Cooper's Algorithm
handle divide terms differently, and we will therefore analyse their
use separately. Here it suffices to say that divide terms and their
negations can be eliminated by introducing existential quantifiers,
which is often not desirable.

\begin{align*}
n ∣ a &\equiv ∃x.\:nx = a \\
n ∤ a &\equiv ∃x.\:\bigvee_{i ∈ 1 \ldots n - 1} nx = (a + i)
\end{align*}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{The Omega Test}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

The Omega Test was first introduced as procedure deciding Presburger
arithmetic in \cite{Pugh1991}. It adapts Fourier-Motzkin elimination —
which acts on real numbers — to integers.

\subsubsection{Building blocks}

To prove our quantifier elimination correct we first need to introduce
the reader to some basic notions involving satisfiability and
decidability of Presburger formulas.

An environment in which to evaluate a formula is a map from de Bruijn
indices to integers, where each index stands for a variable.

The base case for satisfiability is on a single constraint with no
variables, the rest of cases depend on an environment for
substitution.

After substitution, satisfiability is decidable.

\subsubsection{Normalisation}

The Omega Test requires input formulas to be put into disjunctive
normal form. This makes normalisation an expensive exponential
step, as can be clearly seen when cojunctions are normalised over
disjunctions:

\begin{equation*}
(P \lor Q) \land (R \lor S) \equiv (P \land R) \lor (P \land S) \lor
(Q \land R) \lor (Q \land S)
\end{equation*}

The result of normalisation has to be a structure where:
\begin{enumerate*}[label=(\roman*)]
  \item the upper layer is a disjunction;
  \item a disjunction only contains conjunctions; and
  \item a conjunction only contains conjunctions, existential
        quantifiers, negated existential quantifiers, or atoms.
\end{enumerate*}

The following tree-like structure contains ~\AgdaDatatype{Linear}s as
leafs and, within each conjunction, distinguishes leafs from further
subtrees containing existential quantifiers — making it clear which
conjunctions to perform elimination on: on those with no further
subtrees.

As with ~\AgdaDatatype{Formula}s, note that the restriction on the
number of available variables is pushed inside the structure —
~\AgdaDatatype{DNF}~\AgdaBound{n} can only contain
~\AgdaDatatype{Conjunction}~\AgdaBound{n}~ and so forth. The
constructors ~\AgdaInductiveConstructor{∃}~ and
\AgdaInductiveConstructor{¬∃} make one variable more available.

\ExecuteMetaData[Presburger.tex]{normal-form}

Normalisation proceeds recursively, eliminating universal quantifiers,
pushing conjunction and negation inward, normalising implication,
evaluating operations on atoms and normalising relations between them.

\subsubsection{Elimination}

The Omega Test's quantifier elimination operates on quantifier-free
conjunctions of constraints of the form $0 ≤ e$:

\begin{theorem}[Pugh, 1991]
Let $L(x)$ be a conjunction of lower bounds on $x$, indexed by $i$, of
the form $a_i ≤ \alpha_i x$, with $\alpha_i$ positive and
non-zero. Similarly, let $U(x)$ be a set of upper bounds on $x$,
indexed by $j$, of the form $\beta_j x ≤ b_j$, with $\beta_j$ positive
and non-zero. Let $m$ be the maximum of all $\beta_j$s. Then:

\begin{align*}
(∃x.L(x) ∧ U(x)) &\equiv
\left(\bigwedge_{i,j} (\alpha_i - 1)(\beta_j - 1) ≤ (\alpha_i b_j - a_i \beta_j)\right) \\
&\qquad {} \qquad {} \qquad {} \qquad {} \qquad {} \lor \\
&\qquad {} \bigvee_i \bigvee^{\left\lfloor \alpha_i - \frac{\alpha_i}{m} - 1 \right\rfloor}_{k=0}
∃x. (\alpha_i x = a_i + k) \land L(x) \land U(x)
\end{align*}
\end{theorem}

Pugh refers to the first disjunct as the \textit{real shadow} and to
the last as the \textit{splinters}. Each splinter introduces a new
existential quantifier — one could ask if the quantifier elimination
indeed happens. These quantifiers can nonetheless be eliminated by the
following terminating method based on the Euclidean algorithm for the
computation of greatest common divisors:

\begin{align}
  \intertext{$x$ is the variable to eliminate}
  ∃y. ∃x. &\ldots \land ax = by + e \land \ldots \\
  \intertext{Find the lowest common divisor $ℓ$ of coefficients of $x$
        and multiply every constraint by an integer $n$ so that 
        its coeffiecient on $x$ is $ℓ$}
  ∃y. ∃x. &\ldots \land ℓx = b'y + e' \land \ldots \\
  \intertext{Make all coeffients on $x$ be $1$ by resorting to the
        equivalence $P(ℓx) \equiv P(x) \land ℓ ∣ x$.}
  ∃y. ∃x. &\ldots \land (x = b'y + e') \land (ℓ ∣ x) \land \ldots \\
  \intertext{Substitute $x$}
  ∃y. &\ldots \land ℓ ∣ b'y + e' \land \ldots \label{eq:divides} \\
  \intertext{Eliminate the divides term by introducing a new existential}
  ∃y. ∃z. &\ldots \land ℓz = b'y + e' \land \ldots \\
  \intertext{Rearrange}
  ∃y. ∃z. &\ldots \land b'y = ℓz - e' \land \ldots
  \intertext{$y$ is the variable to eliminate} \nonumber
\end{align}

Crucially, \ref{eq:divides} guarantees the eventual elimination of the
divides term, as $b' < ℓ$ — and modulus if not. This recursive
computation is however not trivial to model using structural
recursion. Commonly, structural recursion is applied onto terms that
have been deconstructed by pattern matching — and thus structures get
smaller by "fixed steps". Here, on the other hand, recursion has to be
shown to terminate by account of the divides term's coefficient
decreasing in steps of variable size.

\todo{NatRec}
\todo{Negated divides terms}

However, because of time limitations and the considerable complexity
that implementing the elimination of equalities in splinters and the
proofs involving splinters introduce, we decided to limit the extend
of this chapter to implementing and verifying the soundness of the
real shadow — the first disjunct on the RHS of Pugh's theorem.

\todo{Mention this is a common thing to do}

Pugh's theorem is a sound and complete decision procedure
characterised as a disjunction. Supplying only one of the disjuncts
renders the decision procedure incomplete but does not affect its
soundness. That is: every formula decided true by the dark shadow can
be proven to be true, but no claims can be made about those formulas
that the dark shadow decided false.

Below, we implement quantifier elimination using Pugh's dark-shadow on
quantifier-free formulas.
~\AgdaDatatype{List}~\AgdaSymbol(\AgdaDatatype{Linear}~\AgdaBound{i}\AgdaSymbol{)}~
represents a conjunction over constraints with ~\AgdaBound{i}~
variables, ~\AgdaFunction{partition}~\AgdaBound{as}~ classifies those
constraints into three groups: the lower bounds, with coefficients $0
< c$; the irrelevant constraints, with coefficients $0 = c$; and the
upper bounds, with coefficients $0 > c$ — the second argument, ignored
in this case, is the proof of such inequalities. The symbols $α, a, β,
b$ are as per Pugh. ~\AgdaFunction{×-list}~\AgdaBound{ls}~\AgdaBound{us}~
returns the cartesian product of ~\AgdaBound{ls}~ and ~\AgdaBound{us}.

\todo{Maybe clean}

\ExecuteMetaData[Presburger.tex]{dark-shadow}

For convenience, we will add a shortcut that performs quantifier
elimination as per our incomplete Omega Test, until there are no more
variables left, and then decides the variable-free formula.

\ExecuteMetaData[Presburger.tex]{elimination}

\subsubsection{Verification}

Pugh's theorem is of form $\text{LHS} \equiv D_1 \lor D_2$. That
shapes the proof: it first shows the soundness of both disjuncts by
proving that $D_1 \implies LHS$ and $D_2 \implies \text{LHS}$. Then it
shows the completeness of the theorem by proving that $\text{LHS}
\land \neg D_1 \implies D_2$. By limiting ourselves to implementing
$D_1$, we get a sound but incomplete decision procedure where $D_1
\implies \text{LHS}$ is the only proof obligation:

\begin{equation*}
\bigwedge_{i,j} (\alpha_i - 1)(\beta_i - 1) ≤ \alpha_i b_j - a_i \beta_j
\implies ∃x. L(x) \land U(x)
\end{equation*}

Or, in our terms:

\ExecuteMetaData[Presburger.tex]{correctness}

The original proof uses induction on every $L(x) × U(x)$ pair to prove
the above. The goal for each pair is thus the following:

\begin{equation*}
(\alpha - 1)(\beta - 1) ≤ \alpha b - a \beta \implies ∃x. a ≤ αx \land βx ≤ b
\end{equation*}

This obligation is fulfilled resorting on a proof by contradiction: we
assume $¬∃x. a ≤ αx \land βx ≤ b$ and derive $∃x. a ≤ αx \land βx ≤
b$, in contradiction with the premise which, we conclude, must have
been wrong.  However, we cannot generally imply $P$ from $¬P → ⊥$
in constructive mathematics: the first requires a witness $p : P$ that
the later does not provide.

Nevertheless, a proof by contradiction is still useful. If we can
limit the elements to test for $P$ to a finite set and prove, by
contradiction, that $P$ cannot be false for every element in the set,
then we can supply a terminating function that finds an element
satisfying $P$. We will thus use the proof outlined in
\cite{Norrish2003} to assure the success of our search.

\todo{Explain Σ types somewhere}

Below, a generalised search function that searches for elements
satisfying a decidable predicate within a discrete finite non-empty
search space:

\ExecuteMetaData[Presburger.tex]{search}

In the case that concerns us, the search is for some $x$ that 
satisfies a conjunction of constraints of form $a ≤ \alpha x \land
\beta x ≤ b$, with $\alpha$ and $\beta$ positive and non-zero. For
every constraint, $x$ must be bound between
$\left\lfloor\frac{a}{α}\right\rfloor$ and
$\left\lceil\frac{b}{β}\right\rceil$; the conjunction of all
constraints must be bound between the highest lower bound and the
lowest upper bound.

\ExecuteMetaData[Presburger.tex]{search-space}

Norrish, where each step is implied by the next one

\begin{align*}
&\bigwedge_{\substack{l \in L\\ u \in U}} DS~l~u \implies ∃x. \bigwedge_{\substack{l \in L\\ u \in U}} l~x \land u~x \\
&\bigwedge_{\substack{l \in L\\ u \in U}} DS~l~u \implies \bigwedge_{\substack{l \in L\\ u \in U}} ∃x. l~x \land u~x \\
&\bigwedge_{\substack{l \in L\\ u \in U}} DS~l~u \implies ∃x. l~x \land u~x \\
&\bigwedge_{\substack{l \in L\\ u \in U}} \neg(∃x. l~x \land u~x) \implies \neg(DS~l~u)
\end{align*}

Ours, where each step is implied by the next one

\begin{align*}
&\bigwedge_{\substack{l \in L\\ u \in U}} DS~l~u \implies ∃x. \bigwedge_{\substack{l \in L\\ u \in U}} l~x \land u~x \\
&\bigwedge_{\substack{l \in L\\ u \in U}} DS~l~u \implies \bigwedge_{\substack{l \in L\\ u \in U}} ∃x. l~x \land u~x \\
\neg&\bigwedge_{\substack{l \in L\\ u \in U}} ∃x. l~x \land u~x \implies \neg\bigwedge_{\substack{l \in L\\ u \in U}} DS~l~u \\
&\bigvee_{\substack{l \in L\\ u \in U}} \neg(∃x. l~x \land u~x) \implies \bigvee_{\substack{l \in L\\ u \in U}} \neg(DS~l~u) \\
&\bigwedge_{\substack{l \in L\\ u \in U}} \neg(∃x. l~x \land u~x) \implies \neg(DS~l~u)
\end{align*}


\todo{Introduce proof by contradiction}
\todo{Explain our strategy to make it constructive: bounded search}
\todo{Extract proof obligation}
\todo{Go on with the proof}
\todo{Evaluation, if there is time}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Cooper's Algorithm}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\cite{Cooper1972}
\cite{Chaieb2003}

As part of its existential quantifier elimination step, Cooper's
algorithm requires to have variable coefficients set to $1$ or
$-1$. First, the lowest common multiplier $ℓ$ of all coefficients on
$x$ is computed, then all atoms are multiplied appropriately so that
their coefficient on $x$ becomes equal to the LCM $ℓ$. Finally, all
coefficients are divided by $ℓ$ in accordance to the following
equivalence:

\begin{equation*}
P(ℓx) \equiv P(x) \land ℓ | x
\end{equation*}

\begin{theorem}[Cooper, 1972]
\begin{align*}
∃x.\: P(x) \equiv \bigvee_{j=1}^\delta P_{- \infty} (j) \lor
                  \bigvee_{j=1}^\delta \bigvee_{b \in B} P (b + j)
\end{align*}
\begin{align*}
∃x.\: P(x) \equiv \bigvee_{j=1}^\delta P_{+ \infty} (j) \lor
                  \bigvee_{j=1}^\delta \bigvee_{a \in A} P (a - j)
\end{align*}
\end{theorem}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Future work}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Omega:
  Postulates
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

\begin{appendices}

\chapter{Presburger solver}

% \input{Presburger.lagda}

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

\end{appendices}

\end{document}
