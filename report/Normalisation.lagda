\begin{code}
module Normalisation where

open import Function using (_∘_)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Integer as Int hiding (suc)
open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.List as List using (List ; [] ; _∷_ ; _++_ ; map)

open import Presburger
\end{code}

\section{Normalisation}
\begin{code}
-------------------------------------------
-- Representation of Presburger formulae
\end{code}
%<*formula>
\begin{code}
data Atom (i : ℕ) : Set where
  num' : ℤ               → Atom i
  _+'_ : Atom i → Atom i → Atom i
  _-'_ : Atom i → Atom i → Atom i
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
  -- Introduction of new variables
  ∃'_ ∀'_        : Formula (suc i)       → Formula i
\end{code}
%</formula>

%<*normal-form>
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
%</normal-form>

\begin{code}
open Existential public
open Conjunction public

¬-existential : ∀ {i} → Existential i → Existential i
¬-existential (¬∃ x) = ∃ x
¬-existential (∃ x) = ¬∃ x
  
¬-conjunction : ∀ {i} → Conjunction i → DNF i
¬-conjunction 0≤ cs ∧ bs E = map (λ c → 0≤ ⊘ c ∷ [] ∧                   [] E) cs
                          ++ map (λ b → 0≤       [] ∧ ¬-existential b ∷ [] E) bs
                                                                                             
_∧-dnf_ : ∀ {i} → DNF i → DNF i → DNF i
xs ∧-dnf ys = map 
   (λ {((0≤ cx ∧ bx E) , (0≤ cy ∧ by E)) → 0≤ cx ++ cy ∧ bx ++ by E})
   (×-list xs ys)

_∨-dnf_ : ∀ {i} → DNF i → DNF i → DNF i
_∨-dnf_ = _++_

¬-dnf_ : ∀ {i} → DNF i → DNF i
¬-dnf [] = []
¬-dnf (x ∷ []) = ¬-conjunction x
¬-dnf (x ∷ x' ∷ xs) = ¬-conjunction x ∧-dnf (¬-dnf (x' ∷ xs))
-- ¬-dnf_ = List.foldl (λ dnf conj → dnf ∧-dnf ¬-conjunction conj) (\n

_⇒-dnf_ : ∀ {i} → DNF i → DNF i → DNF i
xs ⇒-dnf ys = (¬-dnf xs) ∨-dnf (xs ∧-dnf ys)

∃-dnf_ : ∀ {i} → DNF (suc i) → DNF i
∃-dnf_ = map λ conj → 0≤ [] ∧ (∃ conj ∷ []) E
                                                   
∀-dnf : ∀ {i} → DNF (suc i) → DNF i
∀-dnf = ¬-dnf_ ∘ ∃-dnf_ ∘ ¬-dnf_

norm-rel : ∀ {i} → Rel → Linear i → Linear i → List (Linear i)
norm-rel <' l₁ l₂ = (l₂ ⊝ l₁) ⊕ (# (- + 1)) ∷ []
norm-rel >' l₁ l₂ = (l₁ ⊝ l₂) ⊕ (# (- + 1)) ∷ []
norm-rel ≤' l₁ l₂ = l₂ ⊝ l₁ ∷ []
norm-rel ≥' l₁ l₂ = l₁ ⊝ l₂ ∷ []
norm-rel =' l₁ l₂ = l₂ ⊝ l₁ ∷ l₁ ⊝ l₂ ∷ []

norm-atom : ∀ {i} → Atom i → Linear i
norm-atom (num' n) = # n
norm-atom (x +' y) = (norm-atom x) ⊕ (norm-atom y)
norm-atom (x -' y) = (norm-atom x) ⊝ (norm-atom y)
norm-atom (n *' x) = n ⊛ (norm-atom x)
norm-atom (var' zero) = (+ 1) x+ ∅
norm-atom (var' (suc n)) with norm-atom (var' n)
...                     | cs ∷+ k = (+ 0) x+ cs +ℤ k
  
norm-form : {i : ℕ} → Formula i → DNF i
norm-form (x ∧' y) = (norm-form x) ∧-dnf (norm-form y)
norm-form (x ∨' y) = (norm-form x) ∨-dnf (norm-form y)
norm-form (x ⇒' y) = (norm-form x) ⇒-dnf (norm-form y)
norm-form (¬' x) = ¬-dnf (norm-form x)
norm-form (∃' x) = ∃-dnf (norm-form x)
norm-form (∀' x) = ∀-dnf (norm-form x)
norm-form (d ∣' x) = 0≤ [] ∧ ∃ 0≤ norm-rel =' ((+ d) x+ ∅) (0x+ norm-atom x) ∧ [] E ∷ [] E ∷ []
norm-form (x [ r ] y) = 0≤ norm-rel r (norm-atom x) (norm-atom y) ∧ [] E ∷ []
\end{code}
