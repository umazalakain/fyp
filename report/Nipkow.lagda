
\begin{code}
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Integer using (ℤ)

open import Prologue

data R : Set where
  [<] [>] [≤] [≥] [=] : R
                      
data T (i : ℕ) : Set where
  num : ℤ → T i
  var : (n : i choose 1) → T i
  _[+]_ : (x y : T i) → T i
  _[*]_ : ℤ → T i → T i
  
data Formula (i : ℕ) : Set where
  rel : T i → R → T i → Formula i
  _[∣]_ : ℤ → T i → Formula i
  _[∧]_ _[∨]_ _[⇒]_ : (x y : Formula i) → Formula i
  [¬]               : (x : Formula i)            → Formula i
  [∃] [∀]           : (x : Formula (suc i))      → Formula i

normalise : ∀ {i} → Formula i → {!!} i
normalise (rel x x₁ x₂) = ?
normalise (x [∣] x₁) = ?
normalise (f [∧] f₁) = ?
normalise (f [∨] f₁) = ?
normalise (f [⇒] f₁) = ?
normalise ([¬] f) = ?
normalise ([∃] f) = ?
normalise ([∀] f) = ?
\end{code}
