\begin{code}
module Demo where

open import Data.Product using (Σ ; _×_ ; _,_)
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.Vec as Vec using (Vec ; _∷_ ; [])
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
\end{code}

























%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% EVIDENCE PRODUCING PROBLEM SOLVERS IN AGDA
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Three problems were selected:
  - Equations on monoids
  - Equations on commutative rings
  - Presburger arithmetic

The solutions to these are not unsupported claims but proven theorems.






















%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% MONOIDS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

- Solved during the first semester
- Made nicer during the second
- A nice warm-up
- Entirely verified

\begin{code}
module _ where
  open import Data.Integer

  open import Monoids
  open Expr
  open Eqn

  -- BY HAND 
  
  ex₁ : {T : Set} (xs ys zs : List T)
      → (xs ++ []) ++ ([] ++ (ys ++ (ys ++ zs)))
      ≡ xs ++ ((ys ++ ys) ++ (zs ++ []))
  
  ex₁ xs ys zs = begin
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
  
  -- AUTOMATICALLY
  
  ex₁-auto : {T : Set}(xs ys zs : List T)
            → (xs ++ []) ++ ([] ++ (ys ++ (ys ++ zs)))
            ≡ xs ++ ((ys ++ ys) ++ (zs ++ []))
  
  ex₁-auto xs ys zs = solve (LIST-MONOID _)
                      (build 3 λ xs ys zs
                             → ((xs ·' ε') ·' (ε' ·' (ys ·' (ys ·' zs))))
                             ≡' (xs ·' ((ys ·' ys) ·' (zs ·' ε'))))
                      (xs ∷ ys ∷ zs ∷ []) 
\end{code}
















%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% COMMUTATIVE RINGS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

- Started researching the problem during winter brake
- Found out Agda's standard library already solves it
- Explored their solution

\begin{code}
module _ where
  open import Data.Nat using (ℕ ; _*_ ; _+_)
  open import Data.Nat.Properties
  open SemiringSolver

  -- BY HAND
  ex₂ : (x r k : ℕ) → 2 + x + (x + (1 + x) * k + r) ≡ r + (1 + x) * (2 + k)
  ex₂ x r k = begin
    (2 + x) + (x + (1 + x) * k + r)
      ≡⟨ sym (+-assoc (2 + x) (x + (1 + x) * k) r) ⟩
    (2 + x) + (x + (1 + x) * k) + r
      ≡⟨ cong (λ ● → ● + r) (sym (+-assoc (2 + x) x ((1 + x) * k)) ) ⟩
    ((2 + x) + x + (1 + x) * k) + r
      ≡⟨ +-comm _ r ⟩
    r + (2 + x + x + (1 + x) * k)
      ≡⟨ cong (λ ● → r + (2 + x + ● + (1 + x) * k)) (sym (*-identityʳ x)) ⟩
    r + (2 + x + x * 1 + (1 + x) * k)
      ≡⟨ cong (λ ● → r + (2 + ● + (1 + x) * k)) (sym (+-*-suc x 1)) ⟩
    r + (2 + x * 2 + (1 + x) * k)
      ≡⟨ cong (λ ● → r + (● + (1 + x) * k)) (sym (*-distribʳ-+ 2 1 x)) ⟩
    r + ((1 + x) * 2 + (1 + x) * k)
      ≡⟨ cong (λ ● → r + ●) (sym (*-distribˡ-+ (1 + x) 2 k)) ⟩
    r + (1 + x) * (2 + k)
      ∎
  
  -- AUTOMATICALLY
  
  ex₂-auto : (x r k : ℕ) → 2 + x + (x + (1 + x) * k + r) ≡ r + (1 + x) * (2 + k)
  ex₂-auto x r k = solve 3 (λ x r k → con 2 :+ x :+ (x :+ (con 1 :+ x) :* k :+ r)
                           := r :+ (con 1 :+ x) :* (con 2 :+ k))
                           refl x r k
\end{code}























%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PRESBURGER ARITHMETIC - THE OMEGA TEST
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

- Started during the second semester
- Considerable time conceiving what a solution looks like
- Limited decision procedure: sound but incomplete
- Original proof by contradiction, made constructive: bounded search & adaptation
- Several postulates remain

- *For demo*, syntax severely limited to existential quantifiers on the outside
- Normalisation does not manage ∀

\begin{code}
module _ where
  open import Data.Nat using (zero ; suc ; s≤s ; z≤n) renaming (_*_ to _ℕ*_ ; _+_ to _ℕ+_)
  open import Data.Integer as Int hiding (suc)
  open import Data.Fin using (Fin ; zero ; suc)
  open import Data.Integer.Properties
  open import Data.Nat.Properties using () renaming (+-identityʳ to ℕ+-identityʳ)

  open import Presburger
  open import Adaptation

  x : ∀ {i} → Atom (2 ℕ+ i)
  x = var' (suc zero)

  y : ∀ {i} → Atom (1 ℕ+ i)
  y = var' zero
  
  -- BY HAND
  -- We have to search for x and y ourselves
  -- Once we find them, the proof is easy
  
  ex₃ : Σ ℤ λ x → Σ ℤ λ y → + 0 < x × x + + 1 < + 2 * y × y < + 4
  ex₃ = (+ 1) , (+ 2) , (+≤+ (s≤s z≤n)) , +≤+ (s≤s (s≤s (s≤s z≤n))) , +≤+ (s≤s (s≤s (s≤s z≤n)))
  
  -- AUTOMATICALLY
  
  ex₃-auto : Σ ℤ λ x → Σ ℤ λ y → + 0 < x × x + + 1 < + 2 * y × y < + 4
  ex₃-auto = solve (∃' ∃' ⦂ ((num' (+ 0) [ <' ] x) ∧' (x +' (num' (+ 1))) [ <' ] ((+ 2) *' y) ∧' y [ <' ] (num' (+ 4)))) 

  -- OTHER THEOREMS

  ex₄-auto : ¬ Σ ℤ λ x → Σ ℤ λ y → y > + 0 × x - y ≥ x
  ex₄-auto =  solve (¬' ∃' ∃' ⦂ y [ >' ] num' (+ 0) ∧' (x -' y) [ ≥' ] x) 
  
  -- FALSE CLAIMS don't typecheck
  -- They produce a result of type ⊤ × ⊤

  ex₅-auto : Σ ℤ λ y → y < y
  ex₅-auto = {!solve (∃' ⦂ (y [ <' ] y))!}

  ¬ex₅-auto : ¬ Σ ℤ λ y → y < y
  ¬ex₅-auto = solve (¬' ∃' ⦂ (y [ <' ] y))

  ex₆-auto : Σ ℤ λ x → Σ ℤ λ y → + 2 * x ≡ + 2 * y + + 1
  ex₆-auto = {! solve (∃' ∃' ⦂ (((+ 2) *' x) [ =' ] (((+ 2) *' y) +' num' (+ 1)))) !}

  -- My decision procedure is sound but incomplete
  -- Some theorems don't typecheck

  ¬ex₈-auto : ¬ Σ ℤ λ x → Σ ℤ λ y → + 2 * x ≡ + 2 * y + + 1
  ¬ex₈-auto =  {! solve (¬' ∃' ∃' ⦂ (((+ 2) *' x) [ =' ] (((+ 2) *' y) +' num' (+ 1)))) !}
\end{code}
