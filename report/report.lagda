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

\begin{abstract}
\todo{Abstract}
% Proving certain theorems can be boring and we want to automate it
% We don't want just the answer, we want a proof that it is the correct answer
\end{abstract}

\section*{Acknowledgements}

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

\section{Proofs as programs; propositions as types}

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

\begin{code}
module _ where
  private
    -- Truth: a type with a single constructor trivial to satisfy
    record ⊤ : Set where
        constructor tt

    -- Falsehood: an uninhabited type with no constructors
    data ⊥ : Set where

    -- Disjunction
    data _⊎_ (A B : Set) : Set where
      inj₁ : A → A ⊎ B
      inj₂ : B → A ⊎ B

    module PrincipleShowcase {A : Set} where
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

\section{Reasoning in Agda}

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

\subsection{The experience of programming in Agda}

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

\subsection{Some peculiarities}

Arguments can be named, allowing subsequent arguments to depend on
them. If an argument can be inferred by the type-checker, the
programmer may choose to make it implicit by naming it and enclosing
it in curly braces. Implicit arguments can later still be explicitly
provided and pattern matched against. If the type of an argument can
be inferred by the type-checker, the programmer may omit it and use
$∀$:

\begin{code}
    -- All numbers are either even or not even
    foo : ∀ {n} → Even n ⊎ (Even n → ⊥)
    foo {zero} = inj₁ tt
    foo {suc zero} = inj₂ λ b → b
    foo {suc (suc n)} = foo {n}
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

\subsection{Datatypes and pattern matching}

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
    bar : ∀ n → {p : Even n} → Even (suc n) → ⊥
    bar zero {p} ()
    bar (suc zero) {()} sp
    bar (suc (suc n)) {p} sp = bar n {p} sp 
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

As a result of pattern matching on $compare m n$ we learn about $m$
and $n$. This is the difference between with abstraction and ordinary
case splitting on the right hand side. \cite{Oury2008} contains other
interesting examples of views.

\subsection{Reasoning about equality}
\todo{Finish section}

Any two terms are considered propositionally equal if they unify with
each other:

\begin{code}
    data _≡_ {A : Set} (x : A) : A → Set where
      refl : x ≡ x
\end{code}

\AgdaRef{\_≡\_} is parametrised by an implicit type $A$ and a value $x
: A$ and indexed by a value in $A$. Given some fixed parameter $x$,
for every $y : A$ $x ≡ y$ is thus a type. The constructor
\AgdaRef{refl} is the only means of constructing a value of type $x ≡
y$ and crucially, it can only construct values where $x ≡ x$ after
normalisation. \todo{Colors}

\begin{code}
    -- Computation of suc zero + suc zero happens at compile time
    -- Both sides normalise to suc (suc zero)
    1+1≡2 : (suc zero + suc zero) ≡ suc (suc zero)
    1+1≡2 = refl
\end{code}

Let us fetch some handy equipment for building proofs. \todo{mention stdlib}

\begin{code}
    module Reasoning {A : Set} where
      -- x and y unify when we pattern match on the first argument
      sym : ∀ {x y : A} → x ≡ y → y ≡ x
      sym refl = refl

      -- x and y unify when we pattern match on the first argument
      -- y ≡ z then becomes x ≡ z
      trans : ∀ {x y z : A} → x ≡ y → y ≡ z → x ≡ z
      trans refl eq = eq

      infix  3 _∎
      infixr 2 _≡⟨⟩_ _≡⟨_⟩_
      infix  1 begin_

      begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
      begin_ x≡y = x≡y

      _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
      _ ≡⟨⟩ x≡y = x≡y

      _≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
      _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

      _∎ : ∀ (x : A) → x ≡ x
      _∎ _ = refl

    open Reasoning

    _⟨_⟩_ : ∀ {A B C : Set} → A → (A → B → C) → B → C
    x ⟨ f ⟩ y = f x y

    cong : {A B : Set}{x y : A} (f : A → B) → x ≡ y → f x ≡ f y
    cong f refl = refl

    _∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
    f ∘ g = {!!}

    map-∘ : {A B C : Set}{n : ℕ} (f : A → B) (g : B → C)
            → ∀ (xs : Vec A n) → map g (map f xs) ≡ map (g ∘ f) xs
    map-∘ f g [] = refl
    map-∘ f g (x ∷ xs) = {!!}
\end{code}

Dependent types allow to model predicate logic with ease. 

\begin{code}
    -- zero + n immediately normalises to n
    0+n≡n : ∀ n → (zero + n) ≡ n
    0+n≡n n = refl

    record Σ (A : Set) (B : A → Set) : Set where
      constructor _,_
      field
        proj₁ : A
        proj₂ : B proj₁

    ∃ : {A : Set} → (A → Set) → Set
    ∃ = Σ _

    pred-0 : ∃ λ n → pred n ≡ n
    pred-0 = zero , refl
\end{code}

\todo{Move before rewrites, introduce their need}
\todo{Explain that n+0≡n is a proof generated for any ℕ}
\todo{Introduce the idea of an automated proof generator}

One could think that proving that $∀ n → (n + zero) ≡ n$ is similar to
proving that $∀ n → (zero + n) ≡ n$, but it is not. Depending on
whether \AgdaRef{\_+\_} case splits on the first or on the second
argument, one of those proofs will be trivial while the other will
require induction.


\begin{code}
    n+0≡n : ∀ n → (n + zero) ≡ n
    n+0≡n zero = refl
    n+0≡n (suc n) with n + zero | n+0≡n n
    n+0≡n (suc n) | .n          | refl = refl

    -- n + zero cannot normalise:
    -- Was n constructed with zero or with suc?
    -- We need to use induction
    -- n+0≡n' : ∀ n → (n + zero) ≡ n
    -- n+0≡n' zero = refl
    -- n+0≡n' (suc n) rewrite n+0≡n' n = refl


    data Dec (P : Set) : Set where
      yes : P       → Dec P
      no  : (P → ⊥) → Dec P

    Decidable : {A : Set} → (A → Set) → Set
    Decidable {A} P = ∀ (x : A) → Dec (P x)

    is-even? : Decidable Even
    is-even? zero = yes tt
    is-even? (suc zero) = no λ b → b
    is-even? (suc (suc n)) = is-even? n
\end{code}

\subsection{Proof by reflection}

\section{Problem solvers and their domains}

\todo{Forward reference solutions}

\section{A comment on Agda-Stdlib}

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
open import Data.Fin.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.List.Pointwise using (decidable-≡)
open import Relation.Nullary using (yes ; no)
open ≡-Reasoning
\end{code}
}

It is not unlikely that while solving some bigger problem, one finds
out that part of it can be modeled as an equation on monoids, and thus
solved by a monoid solver.

Constructing a monoid solver is a good first approach to building
automated solvers: it lacks the complexity of numerous other problems,
yet has the same high-level structure.

\section{Problem description and specification}

\href{https://agda.github.io/agda-stdlib/Algebra.html#1079}{Agda-Stdlib's
definition of a monoid} is based on notions about many other algebraic
structures, and is therefore fairly complex. Instead, we will use our
own definition, which is entirely self-contained and fairly simple. A
monoid is a set:

\begin{code}
record Monoid (M : Set) : Set where
  infix 25 _·_
  field
\end{code}

Together with an associative binary operation \AgdaRef{\_·\_}:

\begin{code}
    _·_ : M → M → M
    law-·-· : (x y z : M) → (x · y) · z ≡ x · (y · z)
\end{code}

And a neutral element \AgdaRef{ε} absorbed on both sides:

\begin{code}
    ε : M
    law-ε-· : (m : M) → ε · m ≡ m
    law-·-ε : (m : M) → m ≡ m · ε
\end{code}

$(ℕ, +, 0)$ and $(ℕ, ·, 1)$ are examples of monoids. Note however that
these also happen to be commutative, while monoids need not be — more
on solving commutative monoids later. An example of a non-commutative
monoid are lists together with the concatenation operation:

\begin{code}
open import Data.List using (List ; [] ; _++_)

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

A solver for monoids should decide whether an equation on monoids
holds for all environments. Without an automated solver, the length of
such a proof can be linear with respect to the size of the monoid.

\begin{code}
by-hand : {T : Set}(xs ys zs : List T) → (xs ++ []) ++ ([] ++ (ys ++ (ys ++ zs))) ≡ xs ++ ((ys ++ ys) ++ (zs ++ []))
by-hand {T} xs ys zs = begin
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
  where open Monoid (LIST-MONOID T)
\end{code}

\section{Design and implementation}


\begin{code}
data Expr (n : ℕ) : Set where
  var' : Fin n           → Expr n
  ε'   :                   Expr n
  _·'_ : Expr n → Expr n → Expr n

data Eqn (n : ℕ) : Set where
  _≡'_ : Expr n → Expr n → Eqn n
\end{code}

\cite{Bruijn1972}
\cite{Walt2012}


\todo{Note on commutative monoids}


Let P = ((0 + x) + (x + y)) and Q = ((x + x) + y). Then Solution P Q
[code] will give back the type ∀ (x y) → P ≡ Q representing an
equality proof between P and Q for all possible assignments. If both
sides were not equivalent, we would get a Failure [code] or some other
trivial type.

We can now define a function solve : (p : P) → (q : Q) → Solution p q
[code]. This function has to give back either the actual equality
proof on all possible assignments, or some trivial value indicating
failure.

The monoid laws can be used to distill an expression’s essence: [code]

P = ((0 + x) + (x + y))  Q = ((x + x) + y)
-- Absorb all neutral elements
P = (x + (x + y))        Q = ((x + x) + y)
-- Associativity doesn't matter
P = x + x + y            Q = x + x + y
-- We don't get any information out of +, it's meaningless
-- Let's translate them into lists
P = x ∷ x ∷ y ∷ []       Q = x ∷ x ∷ y ∷ []

If these two lists are equal, then the expressions they came from must
be equivalent. In other words: given any variable assignment, it
doesn’t matter if we evaluate the original expressions [code] or the
resulting lists [code], the result is the same. Translating them into
lists (free monoids), we get rid of anything that makes two equivalent
expressions constructively different.

Now we only need to prove to Agda that translating expressions into
lists to then evaluate those and evaluating expressions is indeed
equivalent. [code]

 Expr X --evalExpr----.  If
   |                  |  ∀ (e : Expr X) →
exprList              |  evalList (exprList e) ≡ evalExpr e
   |                  |  Then
   v                  v  ∀ (p q : Expr X) →
 List X --evalList--> M  exprList p ≡ exprList q ⇔ evalExpr p ≡ evalExpr q


\begin{code}
NormalForm : ℕ → Set
NormalForm n = List (Fin n)

normalise : ∀ {n} → Expr n → NormalForm n
normalise (var' x) = x ∷ []
normalise ε' = []
normalise (i ·' j) = normalise i ++ normalise j

module _ {M : Set} (monoid : Monoid M) where
  open Monoid monoid

  Env : ℕ → Set
  Env n = Vec M n

  ⟦_⟧n : ∀ {n} → List (Fin n) → Env n → M
  ⟦ [] ⟧n       ρ = ε
  ⟦ (x ∷ xs) ⟧n ρ = (lookup x ρ) · ⟦ xs ⟧n ρ

  ⟦_⟧ : ∀ {n} → Expr n → Env n → M
  ⟦ var' x ⟧   ρ = lookup x ρ
  ⟦ ε' ⟧       ρ = ε
  ⟦ xs ·' ys ⟧ ρ = ⟦ xs ⟧ ρ · ⟦ ys ⟧ ρ

  eval-distr : ∀ {n} (p q : NormalForm n) → (ρ : Env n)
               → ⟦ p ⟧n ρ · ⟦ q ⟧n ρ ≡ ⟦ p ++ q ⟧n ρ

  eval-distr [] q ρ = law-ε-· _
  eval-distr (x ∷ p) q ρ = begin
      ((lookup x ρ) · ⟦ p ⟧n ρ) · ⟦ q ⟧n ρ
    ≡⟨ law-·-· _ _ _ ⟩
      (lookup x ρ) · (⟦ p ⟧n ρ · ⟦ q ⟧n ρ)
    ≡⟨ cong (_·_ (lookup x ρ)) (eval-distr p q ρ) ⟩
      (lookup x ρ) · ⟦ p ++ q ⟧n ρ
    ∎

  eval-commutes : ∀ {n} → (expr : Expr n) → (ρ : Env n)
                  → ⟦ expr ⟧ ρ ≡ ⟦ normalise expr ⟧n ρ

  eval-commutes (var' x) ρ = law-·-ε _
  eval-commutes ε'       ρ = refl
  eval-commutes (p ·' q) ρ rewrite eval-commutes p ρ | eval-commutes q ρ
    = eval-distr (normalise p) (normalise q) ρ

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
    ⟦ normalise p ⟧n ρ
      ≡⟨ cong (λ x → ⟦ x ⟧n ρ) leq  ⟩
    ⟦ normalise q ⟧n ρ
      ≡⟨ sym (eval-commutes q ρ) ⟩
    ⟦ q ⟧ ρ
      ∎

-- This is magic
N-ary : ℕ → Set → Set → Set
N-ary zero A B = B
N-ary (suc n) A B = A → N-ary n A B

_$ⁿ_ : ∀ {n A B} → N-ary n A B → (Vec A n → B)
f $ⁿ [] = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs

vars : ∀ {n} → Vec (Expr n) n
vars = tabulate var'

build : ∀ {A}(n : ℕ) → N-ary n (Expr n) A → A
build n f = f $ⁿ vars {n}

\end{code}

\begin{code}
auto : {T : Set}(xs ys zs : List T) → (xs ++ []) ++ ([] ++ (ys ++ (ys ++ zs))) ≡ xs ++ ((ys ++ ys) ++ (zs ++ []))
auto {T} xs ys zs = solve (LIST-MONOID T)
  (build 3 λ xs ys zs → ((xs ·' ε') ·' (ε' ·' (ys ·' (ys ·' zs)))) ≡' (xs ·' ((ys ·' ys) ·' (zs ·' ε')))) (xs ∷ ys ∷ zs ∷ [])

\end{code}

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
