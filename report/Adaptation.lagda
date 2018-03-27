\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module Adaptation where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Integer as Int using (ℤ ; _+_ ; _-_ ; _*_ ; +_)
open import Data.Fin using (zero ; suc)
open import Data.List as List using (List ; [] ; _∷_ ; _++_)
open import Data.Vec as Vec using (Vec ; [] ; _∷_)
open import Data.Product using (Σ ; _×_ ; _,_)
open import Data.List.All using (All ; [] ; _∷_ ; all)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤ ; tt)
open import Relation.Nullary using (¬_ ; yes ; no)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; inspect ; sym) renaming ([_] to >[_]<)

open import Presburger

data NormalForm (i : ℕ) : Set where
  ∃ : NormalForm (suc i) → NormalForm i
  ¬∃ : NormalForm (suc i) → NormalForm i
  st : List (Linear i) → NormalForm i

⟦_⇓⟧ : ∀ {i} → NormalForm i → Env i → Set
⟦ ∃ nf ⇓⟧ ρ = Σ ℤ λ x → ⟦ nf ⇓⟧ (x ∷ ρ)
⟦ ¬∃ nf ⇓⟧ ρ = ∀ (x : ℤ) → ⟦ nf ⇓⟧ (x ∷ ρ) → ⊥
⟦ st as ⇓⟧ ρ = All ⊨[ ρ /x] as

Ω⇓ : ∀ {i} → NormalForm i → Result
Ω⇓ (∃ nf) = Ω⇓ nf
Ω⇓ (¬∃ nf) with Ω⇓ nf
Ω⇓ (¬∃ nf) | satisfiable = unsatisfiable
Ω⇓ (¬∃ nf) | unsatisfiable = satisfiable
Ω⇓ (¬∃ nf) | undecided = undecided
Ω⇓ (st as) = Ω as

Ω⇓-Sound : NormalForm 0 → Set
Ω⇓-Sound nf with Ω⇓ nf
Ω⇓-Sound nf | undecided = ⊤
Ω⇓-Sound nf | satisfiable = ⟦ nf ⇓⟧ []
Ω⇓-Sound nf | unsatisfiable = ⟦ nf ⇓⟧ [] → ⊥

mutual
  unsat⇓ : ∀ {i} (nf : NormalForm i) → Ω⇓ nf ≡ unsatisfiable → (Σ (Env i) ⟦ nf ⇓⟧) → ⊥
  unsat⇓ (∃ nf) eq with Ω⇓ nf | inspect Ω⇓ nf
  unsat⇓ (∃ nf) () | satisfiable | j
  unsat⇓ (∃ nf) eq | unsatisfiable | >[ eq₁ ]< = λ { (ρ , x , ⊨nf) → unsat⇓ nf eq₁ ((x ∷ ρ) , ⊨nf)}
  unsat⇓ (∃ nf) () | undecided | j
  unsat⇓ (¬∃ nf) eq with Ω⇓ nf | inspect Ω⇓ nf
  unsat⇓ (¬∃ nf) eq | satisfiable | >[ eq₁ ]< with sat⇓ nf eq₁
  unsat⇓ (¬∃ nf) eq | satisfiable | >[ eq₁ ]< | x ∷ ρ , ⊨nf = λ {(ρ' , ⊭nf) → ⊭nf x {!!}}
  unsat⇓ (¬∃ nf) () | unsatisfiable | j
  unsat⇓ (¬∃ nf) () | undecided | j
  unsat⇓ (st as) eq with Ω as | inspect Ω as
  unsat⇓ (st as) () | satisfiable | j
  unsat⇓ (st as) eq | unsatisfiable | >[ eq₁ ]< = unsat as eq₁
  unsat⇓ (st as) () | undecided | j
  
  sat⇓ : ∀ {i} (nf : NormalForm i) → Ω⇓ nf ≡ satisfiable → Σ (Env _) ⟦ nf ⇓⟧
  sat⇓ (∃ nf) eq with Ω⇓ nf | inspect Ω⇓ nf
  sat⇓ (∃ nf) eq | satisfiable | >[ eq₁ ]< with sat⇓ nf eq₁
  sat⇓ (∃ nf) eq | satisfiable | >[ eq₁ ]< | x ∷ ρ , ⊨nf = ρ , x , ⊨nf
  sat⇓ (∃ nf) () | unsatisfiable | _
  sat⇓ (∃ nf) () | undecided | _
  sat⇓ (¬∃ nf) eq with Ω⇓ nf | inspect Ω⇓ nf
  sat⇓ (¬∃ nf) () | satisfiable | j
  sat⇓ (¬∃ nf) eq | unsatisfiable | >[ eq₁ ]< = (Vec.replicate (+ 0)) , λ x ⊨nf → unsat⇓ nf eq₁ ((x ∷ _) , ⊨nf)
  sat⇓ (¬∃ nf) () | undecided | j
  sat⇓ (st as) eq with Ω as | inspect Ω as
  sat⇓ (st as) eq | satisfiable | >[ eq₁ ]< = sat as eq₁
  sat⇓ (st as) () | unsatisfiable | j
  sat⇓ (st as) () | undecided | j

Ω⇓-sound : (nf : NormalForm 0) → Ω⇓-Sound nf
Ω⇓-sound nf with Ω⇓ nf      | inspect Ω⇓ nf
Ω⇓-sound nf | undecided     | _        = tt
Ω⇓-sound nf | unsatisfiable | >[ eq ]< = λ ⊨nf → unsat⇓ nf eq ([] , ⊨nf)
Ω⇓-sound nf | satisfiable   | >[ eq ]< with sat⇓ nf eq
Ω⇓-sound nf | satisfiable   | >[ eq ]< | [] , ⊨nf = ⊨nf

data Constraint (i : ℕ) : Set where
  _[_]_ : Atom i → Rel → Atom i → Constraint i
  _∧'_  : Constraint i → Constraint i → Constraint i

data Expr (i : ℕ) : Set where
  ⦂_  : Constraint i  → Expr i
  ¬'_ : Expr i        → Expr i
  ∃'_ : Expr (suc i)  → Expr i

infixr 20 ∃'_ ¬'_ ⦂_
infixr 25 _∧'_
infix 30 _[_]_

open Atom public
open Rel public

⟦_⟧-atom : ∀ {i} → Atom i → Env i → ℤ
⟦ num' n ⟧-atom ρ = n
⟦ a +' a₁ ⟧-atom ρ = ⟦ a ⟧-atom ρ + ⟦ a₁ ⟧-atom ρ
⟦ a -' a₁ ⟧-atom ρ = ⟦ a ⟧-atom ρ - ⟦ a₁ ⟧-atom ρ
⟦ n *' a ⟧-atom ρ = n * ⟦ a ⟧-atom ρ
⟦ var' zero ⟧-atom (x ∷ ρ) = x
⟦ var' (suc n) ⟧-atom (x ∷ ρ) = ⟦ var' n ⟧-atom ρ

⟦_⟧-constraint : ∀ {i} → Constraint i → Env i → Set
⟦ x ∧' x₂ ⟧-constraint ρ = ⟦ x ⟧-constraint ρ × ⟦ x₂ ⟧-constraint ρ
⟦ x [ <' ] x₂ ⟧-constraint ρ = ⟦ x ⟧-atom ρ Int.< ⟦ x₂ ⟧-atom ρ
⟦ x [ >' ] x₂ ⟧-constraint ρ = ⟦ x ⟧-atom ρ Int.> ⟦ x₂ ⟧-atom ρ
⟦ x [ ≤' ] x₂ ⟧-constraint ρ = ⟦ x ⟧-atom ρ Int.≤ ⟦ x₂ ⟧-atom ρ
⟦ x [ ≥' ] x₂ ⟧-constraint ρ = ⟦ x ⟧-atom ρ Int.≥ ⟦ x₂ ⟧-atom ρ
⟦ x [ =' ] x₂ ⟧-constraint ρ = ⟦ x ⟧-atom ρ ≡ ⟦ x₂ ⟧-atom ρ

⟦_⟧ : ∀ {i} → Expr i → Env i → Set
⟦ ¬' e ⟧ ρ = ⟦ e ⟧ ρ → ⊥
⟦ ∃' e ⟧ ρ = Σ ℤ λ x → ⟦ e ⟧ (x ∷ ρ) 
⟦ ⦂ e ⟧ ρ = ⟦ e ⟧-constraint ρ

do-¬ : ∀ {i} → NormalForm i → NormalForm i
do-¬ (∃ n) = ¬∃ n
do-¬ (¬∃ n) = ∃ n
do-¬ (st as) = st (List.map ⊘_ as)

constraint⇓ : ∀ {i} → Constraint i → List (Linear i)
constraint⇓ (a ∧' b) = constraint⇓ a ++ constraint⇓ b
constraint⇓ (a [ r ] b) = norm-rel r (norm-atom a) (norm-atom b)

expr⇓ : ∀ {i} → Expr i → NormalForm i
expr⇓ (¬' e) = do-¬ (expr⇓ e)
expr⇓ (∃' e) = ∃ (expr⇓ e)
expr⇓ (⦂ e) = st (constraint⇓ e)
                   
postulate ⇓-sound : ∀ {i} (e : Expr i) (ρ : Env i) → ⟦ expr⇓ e ⇓⟧ ρ → ⟦ e ⟧ ρ

Solution : Expr 0 → Set
Solution e with Ω⇓ (expr⇓ e)
Solution e | undecided = ⊤
Solution e | unsatisfiable = ⊤ × ⊤
Solution e | satisfiable = ⟦ e ⟧ []

solve : (e : Expr 0) → Solution e
solve e with Ω⇓ (expr⇓ e) | inspect Ω⇓ (expr⇓ e)
solve e | undecided | _ = tt
solve e | unsatisfiable | _ = tt , tt
solve e | satisfiable | >[ eq ]< with Ω⇓ (expr⇓ e) | Ω⇓-sound (expr⇓ e)
solve e | satisfiable | >[ eq ]< | satisfiable | ⊨⇓e = ⇓-sound e [] ⊨⇓e
solve e | satisfiable | >[ () ]< | unsatisfiable | z
solve e | satisfiable | >[ () ]< | undecided | z 

example₂ : ¬ Σ ℤ λ x → (x Int.< x)
example₂ = solve (¬' ∃' ⦂ var' zero [ <' ] var' zero)
\end{code}
