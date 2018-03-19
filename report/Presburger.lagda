\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}

module Presburger where

open import Function using (id ; _∘_ ; _⟨_⟩_)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Integer hiding (suc)
open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Nat.DivMod using (_div_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec as Vec using (Vec ; [] ; _∷_)
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.List as List using (List ; [] ; _∷_ ; _++_)
open import Data.List.All using (All ; all ; [] ; _∷_)
open import Data.List.Any using (Any ; any ; here ; there)
open import Data.Unit using (⊤ ; tt)
open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Sign as Sign using (Sign)

open import Data.Integer.Properties as IntProp using ()
open import Data.Nat.Properties as NatProp using ()
open import Data.List.All.Properties as AllProp using ()
open import Data.Vec.Properties as VecProp using ()

open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Unary using (Decidable)
open import Relation.Binary using (Tri)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; cong ; sym ; _≢_ ; inspect) renaming ([_] to >[_]<)

open import Agda.Primitive using (lzero) renaming (_⊔_ to _ℓ⊔_)
open import Function.Related using (preorder ; implication)
import Relation.Binary.PreorderReasoning as PRE
module ⇒-Reasoning = PRE (preorder implication lzero) renaming (_∼⟨_⟩_ to _⇒⟨_⟩_; _≈⟨_⟩_ to _≡⟨_⟩_; _≈⟨⟩_ to _≡⟨⟩_)
import Relation.Binary.PartialOrderReasoning as POR
module ≤-Reasoning = POR IntProp.≤-poset renaming (_≈⟨_⟩_ to _≡⟨_⟩_ ; _≈⟨⟩_ to _≡⟨⟩_)
module ≡-Reasoning = Relation.Binary.PropositionalEquality.≡-Reasoning

∀[_]_ : ∀ {a p} {A : Set a} → List A → (A → Set p) → Set (p ℓ⊔ a)
∀[ xs ] P = All P xs 

∃[_]_ : ∀ {a p} {A : Set a} → List A → (A → Set p) → Set (p ℓ⊔ a)
∃[ xs ] P = Any P xs 

×-list : {X Y : Set}(xs : List X)(ys : List Y) → List (X × Y)
×-list xs = List.concat ∘ List.map (λ y → List.map (_, y) xs)
\end{code}

%<*formula>
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
%</formula>

%<*pred>
\begin{code}
pred₁' : Formula 0
pred₁' = ∀' ∃' ((x [ =' ] ((+ 2) *' y))
            ∨' (x [ =' ] (((+ 2) *' y) +' (num' (+ 1)))))
  where
    x = var' (suc zero)
    y = var' zero
\end{code}
%</pred>

%<*linear>
\begin{code}
record Linear (i : ℕ) : Set where
  constructor _∷+_
  field
    cs : Vec ℤ i
    k : ℤ
\end{code}
%</linear>

%<*linear-ops>
\begin{code}
pattern _x+_+ℤ_ c cs k = (c ∷ cs) ∷+ k

infixl 20 _⊕_
infixl 20 _⊝_

#_ : ∀ {i} → ℤ → Linear i
# k = Vec.replicate (+ 0) ∷+ k

∅ : ∀ {i} → Linear i
∅ = Vec.replicate (+ 0) ∷+ (+ 0)

_x+_ : ∀ {i} → ℤ → Linear i → Linear (suc i)
n x+ (cs ∷+ k) = (n ∷ cs) ∷+ k

0x+_ : ∀ {i} → Linear i → Linear (suc i)
0x+_ (cs ∷+ k) = ((+ 0) ∷ cs) ∷+ k

_⊛_ : ∀ {i} → ℤ → Linear i → Linear i
z ⊛ (cs ∷+ k) = Vec.map (z *_) cs ∷+ (z * k)

_⊕_ : ∀ {i} → Linear i → Linear i → Linear i
(cs₁ ∷+ k₁) ⊕ (cs₂ ∷+ k₂) = Vec.zipWith _+_ cs₁ cs₂ ∷+ (k₁ + k₂)

⊝_ : ∀ {i} → Linear i → Linear i
⊝ (cs ∷+ k) = (Vec.map -_ cs) ∷+ (- k)

_⊝_ : ∀ {i} → Linear i → Linear i → Linear i
a ⊝ b = a ⊕ (⊝ b)

⊘_ : ∀ {i} → Linear i → Linear i
⊘_ a = (# (+ 1)) ⊝ a

head : ∀ {i} → Linear (suc i) → ℤ
head (c x+ cs +ℤ k) = c

tail : ∀ {i} → Linear (suc i) → Linear i
tail (c x+ cs +ℤ k) = cs ∷+ k
\end{code}
%</linear-ops>

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
\end{code}

%<*normalisation>
\begin{code}
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
norm-form (d ∣' x) = 0≤ {!!} ∧ [] E ∷ []
norm-form (x [ r ] y) = 0≤ norm-rel r (norm-atom x) (norm-atom y) ∧ [] E ∷ []
\end{code}
%</normalisation>

%<*constraints>
\begin{code}
Irrelevant : ∀ {i} → Linear i → Set
Irrelevant {zero} a = ⊥
Irrelevant {suc n} a = + 0 ≡ head a

LowerBound : ∀ {i} → Linear i → Set
LowerBound {zero} a = ⊥
LowerBound {suc n} a = + 0 < head a

UpperBound : ∀ {i} → Linear i → Set
UpperBound {zero} a = ⊥
UpperBound {suc n} a = + 0 > head a

Constraint : (i : ℕ) (P : Linear i → Set) → Set
Constraint i P = Σ (Linear i) P

Pair : (i : ℕ) → Set
Pair i = Constraint i LowerBound × Constraint i UpperBound

partition : ∀ {i} → List (Linear (suc i))
           → List (Constraint (suc i) LowerBound)
           × List (Constraint (suc i) Irrelevant)
           × List (Constraint (suc i) UpperBound)
partition [] = [] , [] , []
partition (a ∷ as) with IntProp.<-cmp (+ 0) (head a) | partition as
partition (a ∷ as) | Tri.tri< 0>c _ _ | ls , is , us = (a , 0>c) ∷ ls , is , us
partition (a ∷ as) | Tri.tri≈ _ 0=c _ | ls , is , us = ls , (a , 0=c) ∷ is , us
partition (a ∷ as) | Tri.tri> _ _ 0<c | ls , is , us = ls , is , (a , 0<c) ∷ us
\end{code}
%</constraints>

%<*evaluation
\begin{code}
Env : ℕ → Set
Env i = Vec ℤ i

[_/x]_ : ∀ {i d} → Env i → Linear (d Nat.+ i) → Linear d
[_/x]_ {d = zero} [] a = a
[_/x]_ {d = zero} xs (cs ∷+ k) = [] ∷+ Vec.foldr₁ _+_ (k ∷ Vec.zipWith _*_ cs xs)
[_/x]_ {d = suc d} xs (c x+ cs +ℤ k) = c x+ ([ xs /x] (cs ∷+ k))

[_/x]↓_ : ∀ {i} → Env i → Linear i → ℤ
[ ρ /x]↓ a = Linear.k {zero} ([ ρ /x] a)

-- div requires an implicit proof showing its divisor is non-zero
a/α : ∀ {i} → Env i → Constraint (suc i) LowerBound → ℤ
a/α ρ (+_ zero x+ -cs +ℤ -k , (_≤_.+≤+ ()))
a/α ρ (+_ (suc α-1) x+ -cs +ℤ -k , lb) = let a = - [ ρ /x]↓ (-cs ∷+ -k) in sign a ◃ (∣ a ∣ div suc α-1)
a/α ρ (-[1+ n ] x+ -cs +ℤ -k , ())

b/β : ∀ {i} → Env i → Constraint (suc i) UpperBound → ℤ
b/β ρ (+_ c x+ cs +ℤ k , _≤_.+≤+ ())
b/β ρ (-[1+ β-1 ] x+ cs +ℤ k , ub) = let b = [ ρ /x]↓ (cs ∷+ k) in sign b ◃ (∣ b ∣ div suc β-1)
\end{code}
%</evaluation>

%<*meaning>
\begin{code}
⊨⇓ : Linear 0 → Set
⊨⇓ a = (+ 0) ≤ (Linear.k a)
\end{code}
%</meaning>

\begin{code}
⊨[_/x] : ∀ {i} → Env i → Linear i → Set
⊨[ ρ /x] a = ⊨⇓ ([ ρ /x] a)

⊨[_/x]ₚ : ∀ {i} → Env i → Pair i → Set
⊨[ ρ /x]ₚ ((l , _) , (u , _)) = ⊨[ ρ /x] l × ⊨[ ρ /x] u

⊨[_/x]ᵢ : ∀ {i} → Env i → Constraint i Irrelevant → Set
⊨[ ρ /x]ᵢ (ir , _) = ⊨[ ρ /x] ir
\end{code}

%<*meaning-all>
\begin{code}
⊨ : ∀ {i} → List (Linear i) → Set
⊨ {i} as = Σ (Env i) λ ρ → All ⊨[ ρ /x] as
\end{code}
%</meaning-all>

%<*decidability>
\begin{code}
⟦_⟧⇓ : (a : Linear 0) → Dec (⊨⇓ a)
⟦ a ⟧⇓ = (+ 0) ≤? (Linear.k a)

⟦_⟧[_/x] : ∀ {i} → (a : Linear i) → (ρ : Env i) → Dec (⊨[ ρ /x] a)
⟦ a ⟧[ ρ /x] = ⟦ [ ρ /x] a ⟧⇓

⟦_⟧[_/x]ₚ : ∀ {i} → (lu : Pair i) → (ρ : Env i) → Dec (⊨[ ρ /x]ₚ lu)
⟦ ((l , _) , (u , _)) ⟧[ ρ /x]ₚ with ⟦ l ⟧[ ρ /x] | ⟦ u ⟧[ ρ /x]
⟦ (l , _) , u , _ ⟧[ ρ /x]ₚ | yes pl | yes pu = yes (pl , pu)
⟦ (l , _) , u , _ ⟧[ ρ /x]ₚ | _      | no ¬pu = no λ {(_ , pu) → ¬pu pu}
⟦ (l , _) , u , _ ⟧[ ρ /x]ₚ | no ¬pl | _      = no λ {(pl , _) → ¬pl pl}
\end{code}
%</decidability>

%<*dark-shadow>
\begin{code}
dark-shadow : ∀ {i} → Pair (suc i) → Linear i
dark-shadow ((l , _) , (u , _)) with head l | ⊝ (tail l) | - (head u) | tail u
...                             | α | a | β | b = (α ⊛ b) ⊝ (β ⊛ a) ⊝ (# ((α - + 1) * (β - + 1)))
    
omega : ∀ {i} → List (Pair (suc i)) → List (Linear i)
omega = List.map dark-shadow
\end{code}
%</dark-shadow>

\begin{code}
k-out : ∀ {i} (a : Linear i) → (Linear.cs a ∷+ (+ 0)) ⊕ (# (Linear.k a)) ≡ a
k-out (cs ∷+ k) = begin 
  (cs ∷+ (+ 0)) ⊕ (# k)
    ≡⟨⟩
  Vec.zipWith _+_ cs (Vec.replicate (+ 0)) ∷+ ((+ 0) + k)
    ≡⟨ cong (_∷+ ((+ 0) + k)) (VecProp.zipWith-replicate₂ _+_ cs (+ 0)) ⟩
  Vec.map (_+ (+ 0)) cs ∷+ ((+ 0) + k)
    ≡⟨ cong (_∷+ ((+ 0) + k)) (VecProp.map-cong IntProp.+-identityʳ cs) ⟩
  Vec.map id cs ∷+ ((+ 0) + k)
    ≡⟨ cong (_∷+ ((+ 0) + k)) (VecProp.map-id cs) ⟩
  (cs ∷+ ((+ 0) + k))
    ≡⟨ cong (λ ⊚ → cs ∷+ ⊚) (IntProp.+-identityˡ k) ⟩
  (cs ∷+ k)
    ∎

  where open ≡-Reasoning

[_/x]↓-distr : ∀ {i} (ρ : Env i) (a b : Linear i) → [ ρ /x]↓ (a ⊕ b) ≡ [ ρ /x]↓ a + [ ρ /x]↓ b
[ ρ /x]↓-distr a@(csa ∷+ ka) b@(csb ∷+ kb)  = begin 
  [ ρ /x]↓ (a ⊕ b)
    ≡⟨⟩
  Linear.k ([ ρ /x] (Vec.zipWith _+_ csa csb ∷+ (ka + kb)))
    ≡⟨⟩
  Vec.foldr₁ _+_ ((ka + kb) ∷ Vec.zipWith _*_ (Vec.zipWith _+_ csa csb) ρ)
    ≡⟨ {!!} ⟩
  Vec.foldr₁ _+_ ((ka ∷ Vec.zipWith _*_ csa ρ) Vec.++ kb ∷ Vec.zipWith _*_ csb ρ)
    ≡⟨ {!!} ⟩
  (Vec.foldr₁ _+_ (ka ∷ Vec.zipWith _*_ csa ρ)) + (Vec.foldr₁ _+_ (kb ∷ Vec.zipWith _*_ csb ρ))
    ≡⟨⟩
  Linear.k ([ ρ /x] (csa ∷+ ka)) + Linear.k ([ ρ /x] (csb ∷+ kb))
    ≡⟨⟩
  [ ρ /x]↓ a + [ ρ /x]↓ b
    ∎
  where open ≡-Reasoning

[_/x]↓-# : ∀ {i} (ρ : Env i) (k : ℤ) → [ ρ /x]↓ (# k) ≡ k
[_/x]↓-# ρ k = begin 
  [ ρ /x]↓ (# k)
    ≡⟨⟩
  Vec.foldr₁ _+_ (k ∷ Vec.replicate (+ 0))
    ≡⟨⟩
  k + Vec.foldr₁ _+_ (Vec.replicate (+ 0))
    ≡⟨ cong (λ ⊚ → k + ⊚) {!!} ⟩
  k + (+ 0)
    ≡⟨ IntProp.+-identityʳ k ⟩
  k
    ∎
  where open ≡-Reasoning

  
⊝#n≡#-n : ∀ {i} → (n : ℤ) → ⊝_ {i} (# n) ≡ # (- n)
⊝#n≡#-n n = begin 
  ⊝ (# n)
    ≡⟨⟩
  (Vec.map -_ (Vec.replicate (+ 0)) ∷+ (- n))
    ≡⟨ cong (_∷+ (- n)) (VecProp.map-replicate -_ (+ 0) _) ⟩
  # (- n)
    ∎
  where open ≡-Reasoning

0≤n→m-n≤m : (m : ℤ) (n : ℤ) → (+ 0) ≤ n → m - n ≤ m
0≤n→m-n≤m = {!!}

\end{code}
   
%<*norrish-inner-header>
\begin{code}
module norrish-inner (i : ℕ) (ρ : Env i) (xs : List ℤ)
                     (l : Constraint (suc i) LowerBound)
                     (u : Constraint (suc i) UpperBound)
                     where
  α = head (proj₁ l)
  a = ⊝ (tail (proj₁ l))
  0<α = proj₂ l
  β = - (head (proj₁ u))
  b = tail (proj₁ u)
  0<β : + 0 < β
  0<β with head (proj₁ u) | proj₂ u
  0<β | +_ _ | +≤+ ()
  0<β | -[1+_] n | z = +≤+ (Nat.s≤s Nat.z≤n)
  n = a/α ρ l
\end{code}
%</norrish-inner-header>

\begin{code}
  0≤[α-1][β-1] : (+ 0) ≤ (α - + 1) * (β - + 1)
  0≤[α-1][β-1] with α       | 0<α 
  0≤[α-1][β-1] | -[1+_] _   | ()
  0≤[α-1][β-1] | +_ zero    | +≤+ ()
  0≤[α-1][β-1] | +_ (suc n) | _ with β       | 0<β
  0≤[α-1][β-1] | +_ (suc n) | _ | -[1+_] m   | ()
  0≤[α-1][β-1] | +_ (suc n) | _ | +_ zero    | +≤+ ()
  0≤[α-1][β-1] | +_ (suc n) | _ | +_ (suc m) | _ rewrite IntProp.+◃n≡+n (n Nat.* m) = +≤+ Nat.z≤n

  [α-1][β-1] : ℤ
  [α-1][β-1] = (α - + 1) * (β - + 1)
  
  aβ≤αb : Linear i
  aβ≤αb = ((α ⊛ b) ⊝ (β ⊛ a))

  aβ≤αβx≤αb : List (Linear (suc i))
  aβ≤αβx≤αb = ((α * β) x+ ∅) ⊝ (β ⊛ (0x+ a))
            ∷ (α ⊛ (0x+ b)) ⊝ ((α * β) x+ ∅)
            ∷ []

  αβn<aβ≤αb<αβ[n+1] : List (Linear i)
  αβn<aβ≤αb<αβ[n+1] = ((β ⊛ a) ⊝ (# (α * β * n)) ⊝ (# (+ 1)))
                    ∷ (α ⊛ b) ⊝ (β ⊛ a)
                    ∷ ((# (α * β * (n + + 1))) ⊝ (α ⊛ b) ⊝ (# (+ 1)))
                    ∷ []

  α≤αβ[n+1]-αb : Linear i
  α≤αβ[n+1]-αb = (# (α * β * (n + + 1))) ⊝ (α ⊛ b) ⊝ (# α)

  β≤aβ-αβn : Linear i
  β≤aβ-αβn = (β ⊛ a) ⊝ (# (α * β * n)) ⊝ (# β)

  αb-aβ<[α-1][β-1] : Linear i
  αb-aβ<[α-1][β-1] = (# [α-1][β-1]) ⊝ (α ⊛ b) ⊝ (β ⊛ a) ⊝ (# (+ 1))
\end{code}

%<*goal-example>
\begin{code}
  [α-1][β-1]≤αb-aβ : Linear i
  [α-1][β-1]≤αb-aβ = (α ⊛ b) ⊝ (β ⊛ a) ⊝ (# ((α - + 1) * (β - + 1)))
\end{code}
%</goal-example>

%<*norrish-subgoal-1>
\begin{code}
  ⊨βa≤αb : ⊨[ ρ /x] [α-1][β-1]≤αb-aβ → ⊨[ ρ /x] aβ≤αb
  ⊨βa≤αb ⊨ds = begin 
    + 0
      ≤⟨ ⊨ds ⟩
    [ ρ /x]↓ (aβ≤αb ⊝ (# [α-1][β-1]))
      ≡⟨ cong (λ ⊚ → [ ρ /x]↓ (aβ≤αb ⊕ ⊚)) (⊝#n≡#-n [α-1][β-1]) ⟩
    [ ρ /x]↓ (aβ≤αb ⊕ (# (- [α-1][β-1])))
      ≡⟨ [ ρ /x]↓-distr _ _ ⟩
    [ ρ /x]↓ aβ≤αb + [ ρ /x]↓ (# (- [α-1][β-1]))
      ≡⟨ cong (λ ⊚ → [ ρ /x]↓ aβ≤αb + ⊚) ([_/x]↓-# ρ _) ⟩
    [ ρ /x]↓ aβ≤αb + (- [α-1][β-1])
      ≤⟨ 0≤n→m-n≤m _ _ 0≤[α-1][β-1]  ⟩
    [ ρ /x]↓ aβ≤αb
      ∎
    where open ≤-Reasoning
\end{code}
%</norrish-subgoal-1>

%<*norrish-subgoal-2>
\begin{code}
  ⊨αβn<aβ≤αb<αβ[n+1] : ⊨[ ρ /x] aβ≤αb
                     → ¬ (∃[ xs ] (λ x → ⊨[ x ∷ ρ /x]ₚ (l , u)))
                     → All ⊨[ ρ /x] αβn<aβ≤αb<αβ[n+1]
\end{code}
%</norrish-subgoal-2>

\begin{code}
  ⊨αβn<aβ≤αb<αβ[n+1] ⊨p₁ ⊭p₂ = r₁ ∷ r₂ ∷ r₃ ∷ []
    where
      open ≤-Reasoning

      -- ⊭aβ≤αβx≤αb : ¬ ⊨ ((α * β) x+∅ ⊝ ⇑1 (β ⊛ a) ∷ ⇑1 (α ⊛ b) ⊝ ((α * β) x+∅) ∷ [])
      -- ⊭aβ≤αβx≤αb ρ' (⊨p₃ ∷ ⊨p₄ ∷ []) = ⊭p₂ ρ' ({!!} ∷ {!!} ∷ [])

      r₁ = begin
        + 0
          ≤⟨ {!!} ⟩
        [ ρ /x]↓ ((β ⊛ a) ⊝ (# (α * β * n)) ⊝ (# (+ 1)))
          ∎
      r₂ = begin
        + 0
          ≤⟨ {!!} ⟩
        [ ρ /x]↓ ((α ⊛ b) ⊝ (β ⊛ a))
          ∎
      r₃ = begin
        + 0
          ≤⟨ {!!} ⟩
        [ ρ /x]↓ ((# (α * β * (n + + 1))) ⊝ (α ⊛ b) ⊝ (# (+ 1)))
          ∎
\end{code}

%<*norrish-subgoal-3>
\begin{code}
  ⊨α≤αβ[n+1]-αb : All ⊨[ ρ /x] αβn<aβ≤αb<αβ[n+1]
                → ⊨[ ρ /x] α≤αβ[n+1]-αb
\end{code}
%</norrish-subgoal-3>

\begin{code}
  ⊨α≤αβ[n+1]-αb (⊨p₁ ∷ ⊨p₂ ∷ ⊨p₃ ∷ []) = begin 
    + 0
      ≤⟨ {!!} ⟩
    [ ρ /x]↓ α≤αβ[n+1]-αb
      ∎
    where open ≤-Reasoning
\end{code}

%<*norrish-subgoal-4>
\begin{code}
  ⊨β≤aβ-αβn : All ⊨[ ρ /x] αβn<aβ≤αb<αβ[n+1]
            → ⊨[ ρ /x] β≤aβ-αβn
\end{code}
%</norrish-subgoal-4>

\begin{code}
  ⊨β≤aβ-αβn (⊨p₁ ∷ ⊨p₂ ∷ ⊨p₃ ∷ []) = begin 
    + 0
      ≤⟨ {!!} ⟩
    [ ρ /x]↓ β≤aβ-αβn
      ∎
    where open ≤-Reasoning
\end{code}

%<*norrish-subgoal-5>
\begin{code}
  ⊭[α-1][β-1]≤αb-aβ : ⊨[ ρ /x] α≤αβ[n+1]-αb
                    → ⊨[ ρ /x] β≤aβ-αβn
                    → ⊨[ ρ /x] [α-1][β-1]≤αb-aβ
                    → ⊥
\end{code}
%</norrish-subgoal-5>

\begin{code}
  ⊭[α-1][β-1]≤αb-aβ ⊨p₁ ⊨p₂ ⊨ds = {!!} 
\end{code}

%<*search>
\begin{code}
search : {A : Set} {P : A → Set} (P? : Decidable P) (as : List A) 
       → (All (¬_ ∘ P) as → ⊥)
       → Σ A P

search P? []       raa = ⊥-elim (raa [])
search P? (a ∷ as) raa with P? a
search P? (a ∷ as) raa | yes p = a , p
search P? (a ∷ as) raa | no ¬p = search P? as (λ ¬pas → raa (¬p ∷ ¬pas))
\end{code}
%</search>

%<*search-space>
\begin{code}
start : ∀ {i} → Env i → List (Constraint (suc i) LowerBound) → ℤ
start ρ ls = List.foldr _⊔_ (+ 0) (List.map (a/α ρ) ls)

stop : ∀ {i} → Env i → List (Constraint (suc i) UpperBound) → ℤ
stop ρ us = List.foldr _⊓_ (+ 0) (List.map (b/β ρ) us)

search-space : ∀ {i} → Env i → (lus : List (Pair (suc i))) → List ℤ
search-space ρ lus with start ρ (List.map proj₁ lus)
search-space ρ lus | Δ₀ with stop ρ (List.map proj₂ lus) - Δ₀
search-space ρ lus | Δ₀ | + n = List.applyUpTo (λ i → + i + Δ₀) n 
search-space ρ lus | Δ₀ | -[1+ n ] = []
\end{code}
%</search-space>

\begin{code}
module _ {i : ℕ} (ρ : Env i) (xs : List ℤ) where
\end{code}

%<*norrish-type>
\begin{code}
  norrish : (lu : Pair (suc i))
          → ¬ ∃[ xs ] (λ x → ⊨[ x ∷ ρ /x]ₚ lu)
          → ¬ ⊨[ ρ /x] (dark-shadow lu)
\end{code}
%</norrish-type>

%<*norrish>
\begin{code}
  norrish (l , u) ⊭xs ⊨Ωlu = proof
    where
      open norrish-inner i ρ xs l u
      proof : ⊥
      proof with ⊨αβn<aβ≤αb<αβ[n+1] (⊨βa≤αb ⊨Ωlu ) ⊭xs
      proof | ps = ⊭[α-1][β-1]≤αb-aβ (⊨α≤αβ[n+1]-αb ps) (⊨β≤aβ-αβn ps) ⊨Ωlu
\end{code}
%</norrish>

%<*contradiction-adaptation>
\begin{code}
  postulate ∀lus∃xs⇒∃xs∀lus : (lus : List (Pair (suc i)))
                            → (∀[ lus ] (λ lu → ∃[ xs ] (λ x → ⊨[ x ∷ ρ /x]ₚ lu)))
                            → (∃[ xs ] (λ x → ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ))

  ∀xs→¬∀lus⇒∃lus→¬∃xs : (lus : List (Pair (suc i)))
                      → (∀[ xs ] λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
                      → (∃[ lus ] λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)

  ∀xs→¬∀lus⇒∃lus→¬∃xs lus = begin
    (∀[ xs ] λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
      ⇒⟨ AllProp.All¬⇒¬Any ⟩
    (¬ ∃[ xs ] λ x → ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
      ⇒⟨ (λ ¬∃xs∀lus ∀lus∃xs → ¬∃xs∀lus (∀lus∃xs⇒∃xs∀lus lus ∀lus∃xs)) ⟩
    (¬ ∀[ lus ] λ lu → ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
      ⇒⟨ AllProp.¬All⇒Any¬ (λ lu → any (λ x → ⟦ lu ⟧[ x ∷ ρ /x]ₚ) xs) lus ⟩
    (∃[ lus ] λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
      ∎
    where open ⇒-Reasoning
\end{code}
%</contradiction-adaptation>

%<*contradiction-search>
\begin{code}
  ¬∃lus→¬∃xs : (lus : List (Pair (suc i)))
             → (⊨Ωlus : All ⊨[ ρ /x] (omega lus))
             → (∃[ lus ] λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
             → ⊥

  ¬∃lus→¬∃xs [] [] ()
  ¬∃lus→¬∃xs (lu ∷ lus) (⊨Ωlu ∷ ⊨Ωlus) (here ¬∃xs)       = norrish lu ¬∃xs ⊨Ωlu
  ¬∃lus→¬∃xs (lu ∷ lus) (⊨Ωlu ∷ ⊨Ωlus) (there ∃lus→¬∃xs) = ¬∃lus→¬∃xs lus ⊨Ωlus ∃lus→¬∃xs
\end{code}
%</contradiction-search>

%<*by-contradiction-type>
\begin{code}
  by-contradiction : (lus : List (Pair (suc i)))
                   → (⊨Ωlus : All ⊨[ ρ /x] (omega lus))
                   → (∀[ xs ] λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
                   → ⊥
\end{code}
%</by-contradiction-type>

%<*by-contradiction>
\begin{code}
  by-contradiction lus ⊨Ωlus ∀xs¬∀lus =
    ¬∃lus→¬∃xs lus ⊨Ωlus (∀xs→¬∀lus⇒∃lus→¬∃xs lus ∀xs¬∀lus)
\end{code}
%</by-contradiction>

%<*find-x>
\begin{code}
find-x : ∀ {i} (ρ : Env i) (lus : List (Pair (suc i)))
       → All ⊨[ ρ /x] (omega lus)
       → Σ ℤ λ x → All ⊨[ x ∷ ρ /x]ₚ lus

find-x ρ lus ⊨Ωlus with search-space ρ lus
find-x ρ lus ⊨Ωlus | xs = search (λ x → all ⟦_⟧[ x ∷ ρ /x]ₚ lus ) xs (by-contradiction ρ xs lus ⊨Ωlus)
\end{code}
%</find-x>

%<*result>
\begin{code}
data Result : Set where
  satisfiable unsatisfiable undecided : Result
\end{code}
%</result>

\begin{code}
elim-irrel : ∀ {i} → List (Constraint (suc i) Irrelevant) → List (Linear i)
elim-irrel = List.map (tail ∘ proj₁)

exact-α : ∀ {i} → Decidable {A = Constraint (suc i) LowerBound} λ l → + 1 ≡ head (proj₁ l)
exact-α l = + 1 ≟ head (proj₁ l)

exact-β : ∀ {i} → Decidable {A = Constraint (suc i) UpperBound} λ l → - + 1 ≡ head (proj₁ l)
exact-β l = - + 1 ≟ head (proj₁ l)
\end{code}

%<*elimination>
\begin{code}
interpret : ∀ {i} → List (Constraint (suc i) LowerBound)
                  → List (Constraint (suc i) UpperBound)
                  → Result → Result
interpret ls us unsatisfiable with all exact-α ls | all exact-β us
... | no _ | no _ = undecided
... | _    | _    = unsatisfiable
interpret ls us r = r

⟦_⟧Ω : ∀ {i} → List (Linear i) → Result
⟦_⟧Ω {zero} as with all ⟦_⟧[ [] /x] as
...            | yes p = satisfiable
...            | no ¬p = unsatisfiable
⟦_⟧Ω {suc i} as with partition as
...             | ls , is , us = interpret ls us ⟦ elim-irrel is ++ omega (×-list ls us) ⟧Ω 
\end{code}
%</elimination>

%<*correctness>
\begin{code}
⟦_⟧Ω-Correct : ∀ {i} (as : List (Linear i)) → Set
⟦_⟧Ω-Correct as with ⟦ as ⟧Ω
⟦_⟧Ω-Correct as | undecided      = ⊤
⟦_⟧Ω-Correct as | satisfiable    = ⊨ as
⟦_⟧Ω-Correct as | unsatisfiable  = ⊨ as → ⊥
\end{code}
%</correctness>

%<*prepend-x>
\begin{code}
prepend-x : ∀ {i} (ρ : Env i) (x : ℤ) (irs : List (Constraint (suc i) Irrelevant))
          → All ⊨[ ρ /x] (elim-irrel irs)
          → All ⊨[ x ∷ ρ /x]ᵢ irs

prepend-x ρ x [] [] = []
prepend-x ρ x (ir ∷ irs) (⊨Ωir ∷ ⊨Ωirs) = one ρ x ir ⊨Ωir ∷ (prepend-x ρ x irs ⊨Ωirs)
  where
  one : ∀ {i} (ρ : Env i) (x : ℤ) (ir : Constraint (suc i) Irrelevant)
      → (⊨[ ρ /x] ∘ tail ∘ proj₁) ir
      → ⊨[ x ∷ ρ /x]ᵢ ir

  one x ir ⊨Ωir = {!!}
\end{code}
%</prepend-x>

%<*correct>
\begin{code}
foo : ∀ {i} (x : ℤ) (ρ : Env i) (lus : List (Pair (suc i))) → All ⊨[ x ∷ ρ /x]ₚ lus → All ⊨[ ρ /x] (omega lus)
foo x ρ [] [] = []
foo x ρ ((l , u) ∷ lus) ((⊨l , ⊨u) ∷ ⊨lus) = {!!}

unsat : ∀ {i} (as : List (Linear i)) → ⟦ as ⟧Ω ≡ unsatisfiable → ⊨ as → ⊥
unsat {zero} as ep with all ⟦_⟧[ [] /x] as
unsat {zero} as () | yes p
unsat {zero} as ep | no ¬p = λ {([] , ⊨as) → ¬p ⊨as}
unsat {suc i} as ep with partition as
... | ls , irs , us with ×-list ls us
... | lus with ⟦ elim-irrel irs ++ omega lus ⟧Ω | inspect ⟦_⟧Ω (elim-irrel irs ++ omega lus)
unsat {suc i} as () | ls , irs , us | lus | undecided | _
unsat {suc i} as () | ls , irs , us | lus | satisfiable | _
unsat {suc i} as ep | ls , irs , us | lus | unsatisfiable | j with all exact-α ls
unsat {suc i} as ep | ls , irs , us | lus | unsatisfiable | >[ eq ]< | yes ∀α≡1 with unsat (elim-irrel irs ++ omega lus) eq
... | z = λ { ((x ∷ ρ) , ⊨smth) → z (ρ , {!!})}

unsat {suc i} as ep | ls , irs , us | lus | unsatisfiable | j | no _ with all exact-β us
unsat {suc i} as ep | ls , irs , us | lus | unsatisfiable | j | no _ | yes ∀β≡1 = {!!}
unsat {suc i} as () | ls , irs , us | lus | unsatisfiable | j | no _ | no _

sat : ∀ {i} (as : List (Linear i)) → ⟦ as ⟧Ω ≡ satisfiable → ⊨ as
sat {zero} as ep with all ⟦_⟧[ [] /x] as
sat {zero} as ep | yes p = [] , p
sat {zero} as () | no ¬p
sat {suc i} as ep with partition as
... | ls , irs , us with ×-list ls us
... | lus with ⟦ elim-irrel irs ++ omega lus ⟧Ω | inspect ⟦_⟧Ω (elim-irrel irs ++ omega lus)
sat {suc i} as () | ls , irs , us | lus | undecided | _
sat {suc i} as ep | ls , irs , us | lus | unsatisfiable | _ with all exact-α ls
sat {suc i} as () | ls , irs , us | lus | unsatisfiable | _ | yes _
sat {suc i} as ep | ls , irs , us | lus | unsatisfiable | _ | no _  with all exact-β us
sat {suc i} as () | ls , irs , us | lus | unsatisfiable | _ | no _  | yes p
sat {suc i} as () | ls , irs , us | lus | unsatisfiable | _ | no _  | no _ 
sat {suc i} as ep | ls , irs , us | lus | satisfiable  | >[ eq ]< with sat (elim-irrel irs ++ omega lus) eq
sat {suc i} as ep | ls , irs , us | lus | _ | _ | ρ , ⊨Ωas with AllProp.++⁻ (elim-irrel irs) ⊨Ωas
sat {suc i} as ep | ls , irs , us | lus | _ | _ | ρ , ⊨Ωas | ⊨Ωirs , ⊨Ωlus with find-x ρ lus ⊨Ωlus
sat {suc i} as ep | ls , irs , us | lus | _ | _ | ρ , ⊨Ωas | ⊨Ωirs , ⊨Ωlus | x , ⊨lus with prepend-x ρ x irs ⊨Ωirs
... | ⊨irs = {!!}

⟦_⟧Ω-correct : ∀ {i} (as : List (Linear i)) → ⟦ as ⟧Ω-Correct
⟦_⟧Ω-correct as with ⟦ as ⟧Ω | inspect ⟦_⟧Ω as
⟦_⟧Ω-correct as | undecided     | _        = tt
⟦_⟧Ω-correct as | unsatisfiable | >[ eq ]< = unsat as eq
⟦_⟧Ω-correct as | satisfiable   | >[ eq ]< = sat as eq
\end{code}
%</correct>
