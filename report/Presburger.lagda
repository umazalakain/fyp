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

_<?_ : (x y : ℤ) → Dec (x < y)
x <? y with (+ 1 + x) ≤? y
x <? y | yes p = yes p
x <? y | no ¬p = no ¬p
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
open Linear
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
[_/x]_ {d = zero} (x ∷ xs) (c x+ cs +ℤ k) = [ xs /x] (cs ∷+ (k + c * x))
[_/x]_ {d = suc d} xs (c x+ cs +ℤ k) = c x+ ([ xs /x] (cs ∷+ k))

[_/x]⇓_ : ∀ {i} → Env i → Linear i → ℤ
[ ρ /x]⇓ a = k {zero} ([ ρ /x] a)

-- div requires an implicit proof showing its divisor is non-zero
a/α : ∀ {i} → Env i → Constraint (suc i) LowerBound → ℤ
a/α ρ (+_ zero x+ -cs +ℤ -k , (_≤_.+≤+ ()))
a/α ρ (+_ (suc α-1) x+ -cs +ℤ -k , lb) = let a = - [ ρ /x]⇓ (-cs ∷+ -k) in sign a ◃ (∣ a ∣ div suc α-1)
a/α ρ (-[1+ n ] x+ -cs +ℤ -k , ())

b/β : ∀ {i} → Env i → Constraint (suc i) UpperBound → ℤ
b/β ρ (+_ c x+ cs +ℤ k , _≤_.+≤+ ())
b/β ρ (-[1+ β-1 ] x+ cs +ℤ k , ub) = let b = [ ρ /x]⇓ (cs ∷+ k) in sign b ◃ (∣ b ∣ div suc β-1)
\end{code}
%</evaluation>

%<*truth>
\begin{code}
⊨⇓ : Linear 0 → Set
⊨⇓ a = (+ 0) < (Linear.k a)

⊨[_/x] : ∀ {i} → Env i → Linear i → Set
⊨[ ρ /x] a = ⊨⇓ ([ ρ /x] a)

⊨[_/x]ₚ : ∀ {i} → Env i → Pair i → Set
⊨[ ρ /x]ₚ ((l , _) , (u , _)) = ⊨[ ρ /x] l × ⊨[ ρ /x] u

⊨[_/x]ᵢ : ∀ {i} → Env i → Constraint i Irrelevant → Set
⊨[ ρ /x]ᵢ (ir , _) = ⊨[ ρ /x] ir

⊨ : ∀ {i} → List (Linear i) → Set
⊨ {i} as = Σ (Env i) λ ρ → All ⊨[ ρ /x] as

⊨ₚ : ∀ {i} → List (Pair i) → Set
⊨ₚ {i} as = Σ (Env i) λ ρ → All ⊨[ ρ /x]ₚ as
\end{code}
%</truth>

%<*decidability>
\begin{code}
⟦_⟧⇓ : (a : Linear 0) → Dec (⊨⇓ a)
⟦ a ⟧⇓ = (+ 0) <? (Linear.k a)

⟦_⟧[_/x] : ∀ {i} → (a : Linear i) → (ρ : Env i) → Dec (⊨[ ρ /x] a)
⟦ a ⟧[ ρ /x] = ⟦ [ ρ /x] a ⟧⇓

⟦_⟧[_/x]ₚ : ∀ {i} → (lu : Pair i) → (ρ : Env i) → Dec (⊨[ ρ /x]ₚ lu)
⟦ ((l , _) , (u , _)) ⟧[ ρ /x]ₚ with ⟦ l ⟧[ ρ /x] | ⟦ u ⟧[ ρ /x]
⟦ (l , _) , u , _ ⟧[ ρ /x]ₚ | yes pl | yes pu = yes (pl , pu)
⟦ (l , _) , u , _ ⟧[ ρ /x]ₚ | _      | no ¬pu = no λ {(_ , pu) → ¬pu pu}
⟦ (l , _) , u , _ ⟧[ ρ /x]ₚ | no ¬pl | _      = no λ {(pl , _) → ¬pl pl}

⟦_⟧ : ∀ {i} → (as : List (Linear i)) → (ρ : Env i) → Dec (All ⊨[ ρ /x] as)
⟦ as ⟧ ρ = all ⟦_⟧[ ρ /x] as

⟦_⟧ₚ : ∀ {i} → (lus : List (Pair i)) → (ρ : Env i) → Dec (All ⊨[ ρ /x]ₚ lus)
⟦ lus ⟧ₚ ρ = all ⟦_⟧[ ρ /x]ₚ lus
\end{code}
%</decidability>

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
lemma₀ : ∀ {i} (n : ℤ) → ⊝ (#_ {i} n) ≡ #_ {i} (- n)
lemma₀ {i} n = begin
  (⊝ (# n))
    ≡⟨⟩
  (Vec.map -_ (Vec.replicate (+ 0)) ∷+ (- n))
    ≡⟨ cong (λ ⊚ → ((⊚ ∷+ (- n)))) (VecProp.map-replicate -_ (+ 0) _) ⟩
  (Vec.replicate (- + 0) ∷+ (- n))
    ≡⟨⟩
  (# (- n))
    ∎
  where
    open ≡-Reasoning

lemma₁ : ∀ {i} (csa : Vec ℤ i) (ka n : ℤ) → (csa ∷+ ka) ⊕ (# n) ≡ (csa ∷+ (ka + n))
lemma₁ csa ka n = begin 
  (csa ∷+ ka) ⊕ (# n)
    ≡⟨⟩
  Vec.zipWith _+_ csa (cs (# n)) ∷+ (ka + n)
    ≡⟨⟩
  Vec.zipWith _+_ csa (Vec.replicate (+ 0)) ∷+ (ka + n)
    ≡⟨ cong (_∷+ (ka + n)) (VecProp.zipWith-replicate₂ _+_ csa (+ 0)) ⟩
  Vec.map (_+ (+ 0)) csa ∷+ (ka + n)
    ≡⟨ cong (_∷+ (ka + n)) (VecProp.map-cong IntProp.+-identityʳ csa) ⟩
  Vec.map id csa ∷+ (ka + n)
    ≡⟨ cong (_∷+ (ka + n)) (VecProp.map-id csa) ⟩
  csa ∷+ (ka + n)
    ∎
  where open ≡-Reasoning

lemma₂ : ∀ {i} → (n : ℤ) → ⊝_ {i} (# n) ≡ # (- n)
lemma₂ n = begin 
  ⊝ (# n)
    ≡⟨⟩
  (Vec.map -_ (Vec.replicate (+ 0)) ∷+ (- n))
    ≡⟨ cong (_∷+ (- n)) (VecProp.map-replicate -_ (+ 0) _) ⟩
  # (- n)
    ∎
  where open ≡-Reasoning

lemma₃ : (m : ℤ) (n : ℤ) → (+ 0) ≤ n → m - n ≤ m
lemma₃ m n 0≤n = {!!}

lemma₄ : ∀ {i} (ρ : Env i) (csa : Vec ℤ i) (ka : ℤ)
       → [ ρ /x]⇓ (csa ∷+ ka) ≡ ([ ρ /x]⇓ (csa ∷+ (+ 0))) + ka
lemma₄ ρ csa ka = {!!}
\end{code}
   
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
  0<β = proj₂ u
  n = a/α ρ l

  0≤[α-1][β-1] : (+ 0) ≤ (α - + 1) * (β - + 1)
  0≤[α-1][β-1] with α - + 1 | β - + 1
  0≤[α-1][β-1] | +_ n | +_ m with Sign.+ ◃ (n Nat.* m) | IntProp.+◃n≡+n (n Nat.* m)
  0≤[α-1][β-1] | +_ n | +_ m | +_ .(n Nat.* m) | refl = +≤+ Nat.z≤n
  0≤[α-1][β-1] | +_ n | +_ m | -[1+_] _ | ()
  0≤[α-1][β-1] | +_ n | -[1+_] m = {!!}
  0≤[α-1][β-1] | -[1+_] n | m = {!!}


  [α-1][β-1]≤αb-aβ : Linear i
  [α-1][β-1]≤αb-aβ = (α ⊛ b) ⊝ (β ⊛ a) ⊝ (# ((α - + 1) * (β - + 1)))

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
  αb-aβ<[α-1][β-1] = (# ((α - + 1) * (β - + 1))) ⊝ (α ⊛ b) ⊝ (β ⊛ a) ⊝ (# (+ 1))

  ⊨βa≤αb : ⊨[ ρ /x] [α-1][β-1]≤αb-aβ → ⊨[ ρ /x] aβ≤αb
  ⊨βa≤αb ⊨ds with (α ⊛ b) ⊝ (β ⊛ a) | inspect (_⊝_ (α ⊛ b)) (β ⊛ a)
  ... | (csa ∷+ ka) | >[ eq ]< = begin
    + 1
      ≤⟨ ⊨ds ⟩
    [ ρ /x]⇓ ((α ⊛ b) ⊝ (β ⊛ a) ⊝ (# ((α - + 1) * (β - + 1))))
      ≡⟨ cong (λ ⊚ → [ ρ /x]⇓ (⊚ ⊝ (# ((α - + 1) * (β - + 1))))) eq ⟩
    [ ρ /x]⇓ ((csa ∷+ ka) ⊝ (# ((α - + 1) * (β - + 1))))
      ≡⟨ cong (λ ⊚ → [ ρ /x]⇓ ((csa ∷+ ka) ⊕ ⊚)) (lemma₂ ((α - + 1) * (β - + 1))) ⟩
    [ ρ /x]⇓ ((csa ∷+ ka) ⊕ (# (- ((α - + 1) * (β - + 1)))))
      ≡⟨ cong [ ρ /x]⇓_ (lemma₁ csa ka (- ((α - + 1) * (β - + 1)))) ⟩
    [ ρ /x]⇓ (csa ∷+ (ka - (α - + 1) * (β - + 1)))
      ≡⟨ lemma₄ ρ csa _ ⟩
    [ ρ /x]⇓ (csa ∷+ (+ 0)) + (ka - (α - + 1) * (β - + 1))
      ≡⟨ sym (IntProp.+-assoc ([ ρ /x]⇓ (csa ∷+ (+ 0))) ka (- ((α - + 1) * (β - + 1)))) ⟩
    ([ ρ /x]⇓ (csa ∷+ (+ 0)) + ka) - (α - + 1) * (β - + 1)
      ≤⟨ lemma₃ _ _ 0≤[α-1][β-1] ⟩
    [ ρ /x]⇓ (csa ∷+ (+ 0)) + ka
      ≡⟨ sym (lemma₄ ρ csa ka) ⟩
    [ ρ /x]⇓ (csa ∷+ ka)
      ∎
    where open ≤-Reasoning

  ⊨αβn<aβ≤αb<αβ[n+1] : ⊨[ ρ /x] aβ≤αb → ¬ (∃[ xs ] (λ x → ⊨[ x ∷ ρ /x]ₚ (l , u))) → All ⊨[ ρ /x] αβn<aβ≤αb<αβ[n+1]
  ⊨αβn<aβ≤αb<αβ[n+1] ⊨p₁ ⊭p₂ = r₁ ∷ r₂ ∷ r₃ ∷ []
    where
      open ≤-Reasoning

      -- ⊭aβ≤αβx≤αb : ¬ ⊨ ((α * β) x+∅ ⊝ ⇑1 (β ⊛ a) ∷ ⇑1 (α ⊛ b) ⊝ ((α * β) x+∅) ∷ [])
      -- ⊭aβ≤αβx≤αb ρ' (⊨p₃ ∷ ⊨p₄ ∷ []) = ⊭p₂ ρ' ({!!} ∷ {!!} ∷ [])

      r₁ = begin
        + 1
          ≤⟨ {!!} ⟩
        [ ρ /x]⇓ ((β ⊛ a) ⊝ (# (α * β * n)) ⊝ (# (+ 1)))
          ∎
      r₂ = begin
        + 1
          ≤⟨ {!!} ⟩
        [ ρ /x]⇓ ((α ⊛ b) ⊝ (β ⊛ a))
          ∎
      r₃ = begin
        + 1
          ≤⟨ {!!} ⟩
        [ ρ /x]⇓ ((# (α * β * (n + + 1))) ⊝ (α ⊛ b) ⊝ (# (+ 1)))
          ∎

  ⊨α≤αβ[n+1]-αb : All ⊨[ ρ /x] αβn<aβ≤αb<αβ[n+1] → ⊨[ ρ /x] α≤αβ[n+1]-αb
  ⊨α≤αβ[n+1]-αb (⊨p₁ ∷ ⊨p₂ ∷ ⊨p₃ ∷ []) = begin 
    + 1
      ≤⟨ {!!} ⟩
    [ ρ /x]⇓ α≤αβ[n+1]-αb
      ∎
    where open ≤-Reasoning

  ⊨β≤aβ-αβn : All ⊨[ ρ /x] αβn<aβ≤αb<αβ[n+1] → ⊨[ ρ /x] β≤aβ-αβn
  ⊨β≤aβ-αβn (⊨p₁ ∷ ⊨p₂ ∷ ⊨p₃ ∷ []) = begin 
    + 1
      ≤⟨ {!!} ⟩
    [ ρ /x]⇓ β≤aβ-αβn
      ∎
    where open ≤-Reasoning

  ⊭[α-1][β-1]≤αb-aβ : ⊨[ ρ /x] α≤αβ[n+1]-αb
                    → ⊨[ ρ /x] β≤aβ-αβn
                    → ⊨[ ρ /x] [α-1][β-1]≤αb-aβ
                    → ⊥
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
search-space ρ lus | Δ₀ with Δ₀ - stop ρ (List.map proj₂ lus)
search-space ρ lus | Δ₀ | + n = List.applyUpTo (λ i → + i + Δ₀) n 
search-space ρ lus | Δ₀ | -[1+ n ] = []
\end{code}
%</search-space>

%<*norrish>
\begin{code}
norrish : ∀ {i} (ρ : Env i) (lu : Pair (suc i)) {xs : List ℤ}
        → ¬ ∃[ xs ] (λ x → ⊨[ x ∷ ρ /x]ₚ lu)
        → ¬ ⊨[ ρ /x] (dark-shadow lu)

norrish {i} ρ (l , u) {xs} ⊭xs ⊨Ωlu = proof
  where
    open norrish-inner i ρ xs l u
    proof : ⊥
    proof with ⊨αβn<aβ≤αb<αβ[n+1] (⊨βa≤αb ⊨Ωlu ) ⊭xs
    proof | ps = ⊭[α-1][β-1]≤αb-aβ (⊨α≤αβ[n+1]-αb ps) (⊨β≤aβ-αβn ps) ⊨Ωlu
\end{code}
%</norrish>


%<*contradiction>
\begin{code}
module _ {i : ℕ} (ρ : Env i) where

  ∀lus∃xs⇒∃xs∀lus : (lus : List (Pair (suc i))) (xs : List ℤ)
                  → (∀[ lus ] (λ lu → ∃[ xs ] (λ x → ⊨[ x ∷ ρ /x]ₚ lu)))
                  → (∃[ xs ] (λ x → ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ))
  ∀lus∃xs⇒∃xs∀lus lus xs ∀lus∃xs = {!!}

  ∀xs→¬∀lus⇒∃lus→¬∃xs : (lus : List (Pair (suc i))) (xs : List ℤ)
                      → (∀[ xs ] λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
                      → (∃[ lus ] λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
  ∀xs→¬∀lus⇒∃lus→¬∃xs lus xs = begin
    (∀[ xs ] λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
      ⇒⟨ AllProp.All¬⇒¬Any ⟩
    (¬ ∃[ xs ] λ x → ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
      ⇒⟨ (λ ¬∃xs∀lus ∀lus∃xs → ¬∃xs∀lus (∀lus∃xs⇒∃xs∀lus lus xs ∀lus∃xs)) ⟩
    (¬ ∀[ lus ] λ lu → ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
      ⇒⟨ AllProp.¬All⇒Any¬ (λ lu → any (λ x → ⟦ lu ⟧[ x ∷ ρ /x]ₚ) xs) lus ⟩
    (∃[ lus ] λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
      ∎
    where
    open ⇒-Reasoning
                      
  by-contradiction : (lus : List (Pair (suc i))) (xs : List ℤ)
                   → (⊨Ωlus : All ⊨[ ρ /x] (omega lus))
                   → (∀[ xs ] λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
                   → ⊥
  by-contradiction lus xs  ⊨Ωlus ∀xs¬∀lus = inner lus ⊨Ωlus (∀xs→¬∀lus⇒∃lus→¬∃xs lus xs ∀xs¬∀lus)
    where
    inner : (lus : List (Pair (suc i)))
          → (⊨Ωlus : All ⊨[ ρ /x] (omega lus))
          → (∃[ lus ] λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
          → ⊥
    inner [] [] ()
    inner (lu ∷ lus) (⊨Ωlu ∷ ⊨Ωlus) (here ¬∃xs)       = norrish ρ lu ¬∃xs ⊨Ωlu
    inner (lu ∷ lus) (⊨Ωlu ∷ ⊨Ωlus) (there ∃lus→¬∃xs) = inner lus ⊨Ωlus ∃lus→¬∃xs
\end{code}
%</contradiction>

%<*find-x>
\begin{code}
  find-x : ∀ (lus : List (Pair (suc i)))
         → All ⊨[ ρ /x] (omega lus)
         → Σ ℤ λ x → All ⊨[ x ∷ ρ /x]ₚ lus

  find-x lus ⊨Ωlus with search-space ρ lus
  find-x lus ⊨Ωlus | xs = search (λ x → all ⟦_⟧[ x ∷ ρ /x]ₚ lus ) xs (by-contradiction lus xs ⊨Ωlus)
\end{code}
%</find-x>

    
\begin{code}
elim-irrel : ∀ {i} → List (Constraint (suc i) Irrelevant) → List (Linear i)
elim-irrel = List.map (tail ∘ proj₁)

data EnvTree : Set where
  var     : ℤ → EnvTree
  sub-env : List EnvTree → EnvTree

⟦_⟧Ω' : DNF 0 → Bool
⟦ dnf ⟧Ω' = {!!}
  where
  open import Data.Bool
  mutual
    eval-conjunction : ∀ {i} → Conjunction i → Bool
    eval-conjunction {zero} 0≤ cs ∧ es E = {!!}
    eval-conjunction {suc i} 0≤ cs ∧ es E = {!!}

    eval-existential : ∀ {i} → Existential i → Bool
    eval-existential (¬∃ x) = false -- TODO: explain
    eval-existential (∃ x) = {!!}

\end{code}

%<*elimination>
\begin{code}
⟦_⟧Ω : ∀ {i} → List (Linear i) → Bool
⟦_⟧Ω {zero} as with ⟦ as ⟧ []
...           | yes p = true
...           | no ¬p = false
⟦_⟧Ω {suc i} as with partition as
...             | ls , is , us = ⟦ elim-irrel is ++ omega (×-list ls us) ⟧Ω
\end{code}
%</elimination>

%<*correctness>
\begin{code}
⟦_⟧Ω-Correct : ∀ {i} (as : List (Linear i)) → Set
⟦_⟧Ω-Correct as with ⟦ as ⟧Ω
⟦_⟧Ω-Correct as | false = ⊤
⟦_⟧Ω-Correct as | true  = ⊨ as
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
⟦_⟧Ω-correct : ∀ {i} (as : List (Linear i)) → ⟦ as ⟧Ω-Correct
⟦_⟧Ω-correct as with ⟦ as ⟧Ω | inspect ⟦_⟧Ω as
⟦_⟧Ω-correct as | false | j = tt
⟦_⟧Ω-correct as | true | >[ eq ]< = inner as eq
  where
  
  inner : ∀ {i} (as : List (Linear i)) → ⟦ as ⟧Ω ≡ true → ⊨ as
  inner {zero} as ep with ⟦ as ⟧ []
  inner {zero} as ep | yes p = [] , p
  inner {zero} as () | no ¬p
  inner {suc i} as ep with partition as
  ... | ls , irs , us with ×-list ls us
  ... | lus with ⟦ elim-irrel irs ++ omega lus ⟧Ω | inspect ⟦_⟧Ω (elim-irrel irs ++ omega lus)
  inner {suc i} as () | _ , irs , _ | lus | false | _
  inner {suc i} as ep | _ , irs , _ | lus | true  | >[ eq ]< with inner (elim-irrel irs ++ omega lus) eq
  inner {suc i} as ep | _ , irs , _ | lus | _ | _ | ρ , ⊨Ωas with AllProp.++⁻ (elim-irrel irs) ⊨Ωas
  inner {suc i} as ep | _ , irs , _ | lus | _ | _ | ρ , ⊨Ωas | ⊨Ωirs , ⊨Ωlus with find-x ρ lus ⊨Ωlus
  inner {suc i} as ep | _ , irs , _ | lus | _ | _ | ρ , ⊨Ωas | ⊨Ωirs , ⊨Ωlus | x , ⊨lus with prepend-x ρ x irs ⊨Ωirs
  ... | ⊨irs = {!!}
\end{code}
%</correct>
