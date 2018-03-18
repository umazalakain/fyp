\begin{code}
module Monoids where

open import Data.Unit using (⊤ ; tt)
open import Data.List using (List ; [] ; _∷_ ; _++_)
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

%<*monoid>
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
%</monoid>

%<*list-monoid>
\begin{code}
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
%</list-monoid>

%<*eqn1>
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
%</eqn1>

%<*eqn2>
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
%</eqn2>

%<*expr>
\begin{code}
data Expr (n : ℕ) : Set where
  var' : Fin n           → Expr n
  ε'   :                   Expr n
  _·'_ : Expr n → Expr n → Expr n

data Eqn (n : ℕ) : Set where
  _≡'_ : Expr n → Expr n → Eqn n
\end{code}
%</expr>

%<*normal-form>
\begin{code}
NormalForm : ℕ → Set
NormalForm n = List (Fin n)
\end{code}
%</normal-form>

\begin{code}
_≟_ : ∀ {n} → Decidable {A = List (Fin n)} _≡_
_≟_ = List-≟ _Fin-≟_ 
\end{code}

%<*normalise>
\begin{code}
normalise : ∀ {n} → Expr n → NormalForm n
normalise (var' i)   = i ∷ []
normalise ε'         = []
normalise (e₁ ·' e₂) = normalise e₁ ++ normalise e₂
\end{code}
%</normalise>

%<*monoid-module>
\begin{code}
module _ {M : Set} (monoid : Monoid M) where
  open Monoid monoid
\end{code}
%</monoid-module>

%<*env>
\begin{code}
  Env : ℕ → Set
  Env n = Vec M n
\end{code}
%</env>

%<*evaluation>
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
%</evaluation>

%<*solution>
\begin{code}
  Solution : ∀ {n} → Eqn n → Set
  Solution {n} (e₁ ≡' e₂) with (normalise e₁) ≟ (normalise e₂)
  ...                     | no  _ = ⊤
  ...                     | yes _ = ∀ (ρ : Env n) → ⟦ e₁ ⟧ ρ ≡ ⟦ e₂ ⟧ ρ
\end{code}
%</solution>

%<*solve-type>
\begin{code}
  solve : ∀ {n} (eqn : Eqn n) → Solution eqn
\end{code}
%</solve-type>

%<*eval-commutes-type>
\begin{code}
  eval-commutes : ∀ {n} → (e : Expr n) → (ρ : Env n)
                  → ⟦ e ⟧ ρ ≡ ⟦ normalise e ⇓⟧ ρ
\end{code}
%</eval-commutes-type>

%<*solve>
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
%</solve>

%<*eval-commutes>
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
%</eval-commutes>

%<*eqn1-auto>
\begin{code}
eqn₁-auto : {T : Set}(xs : List T) → [] ++ xs ≡ xs ++ []
eqn₁-auto xs = solve (LIST-MONOID _)
               ((ε' ·' var' zero) ≡' (var' zero ·' ε')) (xs ∷ [])
\end{code}
%</eqn1-auto>

\begin{code}
_$ⁿ_ : ∀ {n}{A B : Set} → N-ary n A B → (Vec A n → B)
f $ⁿ [] = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs

vars : ∀ {n} → Vec (Expr n) n
vars = tabulate var'

build : ∀ {A}(n : ℕ) → N-ary n (Expr n) A → A
build n f = f $ⁿ vars {n}
\end{code}

%<*eqn2-auto>
\begin{code}
eqn₂-auto : {T : Set}(xs ys zs : List T)
          → (xs ++ []) ++ ([] ++ (ys ++ (ys ++ zs)))
          ≡ xs ++ ((ys ++ ys) ++ (zs ++ []))

eqn₂-auto xs ys zs = solve (LIST-MONOID _) (build 3 λ xs ys zs
                   → ((xs ·' ε') ·' (ε' ·' (ys ·' (ys ·' zs))))
                   ≡' (xs ·' ((ys ·' ys) ·' (zs ·' ε')))) (xs ∷ ys ∷ zs ∷ [])
\end{code}
%</eqn2-auto>

\begin{code}
postulate
  magic-solve : {T : Set} (m : Monoid (List T)) (xs ys zs : List T)
                → (xs ++ []) ++ ([] ++ (ys ++ (ys ++ zs)))
                ≡ xs ++ ((ys ++ ys) ++ (zs ++ []))
\end{code}

%<*eqn2-magic>
\begin{code}
eqn₂-magic : {T : Set}(xs ys zs : List T)
           → (xs ++ []) ++ ([] ++ (ys ++ (ys ++ zs)))
           ≡ xs ++ ((ys ++ ys) ++ (zs ++ []))

eqn₂-magic = magic-solve (LIST-MONOID _)
\end{code}
%</eqn2-magic>
