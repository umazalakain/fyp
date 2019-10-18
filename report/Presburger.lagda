\begin{code}
-----------------------------------------------------------------------------------------
-- Verified decision procedure for quantifier-free conjunctions of Presburger formulae --
-- Implements the Omega Test. It is still a work in progress                           --
-----------------------------------------------------------------------------------------

module Presburger where

open import Function using (id ; _∘_)

-- Data types
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Integer as Int hiding (suc)
open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Nat.Divisibility as Div
open import Data.Nat.DivMod using (_div_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec as Vec using (Vec ; [] ; _∷_)
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.List as List using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.List.All using (All ; all ; [] ; _∷_)
open import Data.List.Any using (Any ; any ; here ; there)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

-- Properties
open import Data.Integer.Properties as IntProp using ()
open import Data.Nat.Properties as NatProp using ()
open import Data.List.All.Properties as AllProp using ()
open import Data.Vec.Properties as VecProp using ()

-- Relations
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Unary using (Decidable)
open import Relation.Binary using (Tri)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; cong ; sym ; _≢_ ; inspect) renaming ([_] to >[_]<)

-- Implication reasoning
open import Agda.Primitive using (lzero) renaming (_⊔_ to _ℓ⊔_)
open import Function.Related using (K-preorder ; implication)
import Relation.Binary.PreorderReasoning as PRE
module ⇒-Reasoning = PRE (K-preorder implication lzero)
open Function.Related using (≡⇒)

-- Partial order reasoning
import Relation.Binary.PartialOrderReasoning as POR
module ≤-Reasoning = POR IntProp.≤-poset

-- Equality reasoning
module ≡-Reasoning = Relation.Binary.PropositionalEquality.≡-Reasoning

-----------
-- UTILS

-- I don't have time for these
postulate x≤y+z≡x-z≤y : (x y z : ℤ) → (x ≤ y + z) ≡ (x - z ≤ y)
postulate 0≤n→m-n≤m : (m : ℤ) (n : ℤ) → (+ 0) ≤ n → m - n ≤ m

-- Show the predicate subject immediately (useful with nested predicates)
∀[_]_ : ∀ {a p} {A : Set a} → List A → (A → Set p) → Set (p ℓ⊔ a)
∀[ xs ] P = All P xs

∃[_]_ : ∀ {a p} {A : Set a} → List A → (A → Set p) → Set (p ℓ⊔ a)
∃[ xs ] P = Any P xs

-- Cartesian product of two lists
×-list : {X Y : Set} → List X → List Y → List (X × Y)
×-list xs = List.concatMap λ y → map (_, y) xs

-- Generic bounded search function
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

\begin{code}
----------------------------------------------
-- Individual linear constraints 0 ≤ cs + k

\end{code}

%<*linear>
\begin{code}
record Linear (i : ℕ) : Set where
  constructor _∷+_
  field
    cs : Vec ℤ i
    k : ℤ
\end{code}
%</linear>

\begin{code}
--------------------------------------
-- Utilities for linear constraints

\end{code}

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
⊘_ a = (# (- + 1)) ⊝ a

head : ∀ {i} → Linear (suc i) → ℤ
head (c x+ cs +ℤ k) = c

tail : ∀ {i} → Linear (suc i) → Linear i
tail (c x+ cs +ℤ k) = cs ∷+ k
\end{code}
%</linear-ops>

\begin{code}
--------------------------------
--- Constraint classification

Irrelevant : ∀ {i} → Linear i → Set
Irrelevant {zero} a = ⊥
Irrelevant {suc n} a = + 0 ≡ head a

LowerBound : ∀ {i} → Linear i → Set
LowerBound {zero} a = ⊥
LowerBound {suc n} a = + 0 < head a

UpperBound : ∀ {i} → Linear i → Set
UpperBound {zero} a = ⊥
UpperBound {suc n} a = + 0 > head a
\end{code}

%<*pair>
\begin{code}
Pair : (i : ℕ) → Set
Pair i = Σ (Linear i) LowerBound × Σ (Linear i) UpperBound
\end{code}
%</pair>

\begin{code}
partition : ∀ {i} → List (Linear (suc i))
           → List (Σ (Linear (suc i)) LowerBound)
           × List (Σ (Linear (suc i)) Irrelevant)
           × List (Σ (Linear (suc i)) UpperBound)
partition [] = [] , [] , []
partition (a ∷ as) with IntProp.<-cmp (+ 0) (head a) | partition as
partition (a ∷ as) | Tri.tri< 0>c _ _ | ls , is , us = (a , 0>c) ∷ ls , is , us
partition (a ∷ as) | Tri.tri≈ _ 0=c _ | ls , is , us = ls , (a , 0=c) ∷ is , us
partition (a ∷ as) | Tri.tri> _ _ 0<c | ls , is , us = ls , is , (a , 0<c) ∷ us

-- Careful not to pattern match on the result of partition as:
-- We want Agda to see where the result comes from
pairs : ∀ {i} (as : List (Linear (suc i))) → List (Pair (suc i))
pairs as = let lius = partition as in ×-list (proj₁ lius) (proj₂ (proj₂ lius))
irrels : ∀ {i} (as : List (Linear (suc i))) → List (Σ (Linear (suc i)) Irrelevant)
irrels as = proj₁ (proj₂ (partition as))
\end{code}

\begin{code}
-----------------
-- Elimination

\end{code}
%<*dark-shadow>
\begin{code}
_↓ₚ : ∀ {i} → Pair (suc i) → Linear i
((l , _) , (u , _)) ↓ₚ with head l | ⊝ (tail l) | - (head u) | tail u
...                    | α | a | β | b = (α ⊛ b) ⊝ (β ⊛ a) ⊝ (# ((α - + 1) * (β - + 1)))
\end{code}
%</dark-shadow>

\begin{code}
_↓ᵢ : ∀ {i} → Σ (Linear (suc i)) Irrelevant → Linear i
_↓ᵢ = tail ∘ proj₁

_↓ : ∀ {i} → List (Linear (suc i)) → List (Linear i)
as ↓ = map _↓ᵢ (irrels as) ++ map _↓ₚ (pairs as)
\end{code}

\begin{code}
---------------------------------
-- Foundations of verification
\end{code}
\begin{code}
Env : ℕ → Set
Env i = Vec ℤ i

[_/x]_ : ∀ {i} → Env i → Linear i → ℤ
[_/x]_ [] ([] ∷+ k) = k
[_/x]_ (x ∷ xs) ((c ∷ cs) ∷+ k) = c * x + [ xs /x] (cs ∷+ k)
\end{code}

%<*meaning>
\begin{code}
⊨[_/x] : ∀ {i} → Env i → Linear i → Set
⊨[ ρ /x] a = + 0 ≤ ([ ρ /x] a)
\end{code}
%</meaning>

\begin{code}
⊨[_/x]ₚ : ∀ {i} → Env i → Pair i → Set
⊨[ ρ /x]ₚ ((l , _) , (u , _)) = ⊨[ ρ /x] l × ⊨[ ρ /x] u

⊨[_/x]ᵢ : ∀ {i} → Env i → Σ (Linear i) Irrelevant → Set
⊨[ ρ /x]ᵢ (ir , _) = ⊨[ ρ /x] ir
⊨?_[_/x] : ∀ {i} → (a : Linear i) → (ρ : Env i) → Dec (⊨[ ρ /x] a)
⊨? a [ ρ /x] = + 0 ≤? [ ρ /x] a

⊨?_[_/x]ₚ : ∀ {i} → (lu : Pair i) → (ρ : Env i) → Dec (⊨[ ρ /x]ₚ lu)
⊨? ((l , _) , (u , _)) [ ρ /x]ₚ with ⊨? l [ ρ /x] | ⊨? u [ ρ /x]
⊨? (l , _) , u , _ [ ρ /x]ₚ | yes pl | yes pu = yes (pl , pu)
⊨? (l , _) , u , _ [ ρ /x]ₚ | _      | no ¬pu = no λ {(_ , pu) → ¬pu pu}
⊨? (l , _) , u , _ [ ρ /x]ₚ | no ¬pl | _      = no λ {(pl , _) → ¬pl pl}
\end{code}

%<*meaning-all>
\begin{code}
⊨ : ∀ {i} → List (Linear i) → Set
⊨ {i} as = Σ (Env i) λ ρ → ∀[ as ] ⊨[ ρ /x]
\end{code}
%</meaning-all>

\begin{code}
-----------------------------------------
-- Verification lemmas & homomorphisms

[_/x]-⊕ : ∀ {i} (ρ : Env i) (a b : Linear i) → [ ρ /x] (a ⊕ b) ≡ [ ρ /x] a + [ ρ /x] b
[ [] /x]-⊕ ([] ∷+ ka) ([] ∷+ kb) = refl
[ x ∷ ρ /x]-⊕ ((ca ∷ csa) ∷+ ka) ((cb ∷ csb) ∷+ kb)
  rewrite [ ρ /x]-⊕ (csa ∷+ ka) (csb ∷+ kb) = begin
  (ca + cb) * x + ([ ρ /x] (csa ∷+ ka) + [ ρ /x] (csb ∷+ kb))
    ≡⟨ cong (λ ● → ● + _) (IntProp.*-distribʳ-+ x ca cb) ⟩
  (ca * x + cb * x) + ([ ρ /x] (csa ∷+ ka) + [ ρ /x] (csb ∷+ kb))
    ≡⟨ IntProp.+-assoc (ca * x) (cb * x) _ ⟩
  ca * x + (cb * x + ([ ρ /x] (csa ∷+ ka) + [ ρ /x] (csb ∷+ kb)))
    ≡⟨ cong (λ ● → ca * x + ●) (sym (IntProp.+-assoc (cb * x) _ _)) ⟩
  ca * x + (cb * x + [ ρ /x] (csa ∷+ ka) + [ ρ /x] (csb ∷+ kb))
    ≡⟨ cong (λ ● → ca * x + (● + _)) (IntProp.+-comm (cb * x) ([ ρ /x] (csa ∷+ ka))) ⟩
  ca * x + ([ ρ /x] (csa ∷+ ka) + cb * x + [ ρ /x] (csb ∷+ kb))
    ≡⟨ cong (λ ● → ca * x + ●) (IntProp.+-assoc ([ ρ /x] (csa ∷+ ka)) (cb * x) _) ⟩
  ca * x + ([ ρ /x] (csa ∷+ ka) + (cb * x + [ ρ /x] (csb ∷+ kb)))
    ≡⟨ sym (IntProp.+-assoc (ca * x) ([ ρ /x] (csa ∷+ ka)) _) ⟩
  (ca * x + [ ρ /x] (csa ∷+ ka)) + (cb * x + [ ρ /x] (csb ∷+ kb))
    ∎
  where open ≡-Reasoning

[_/x]-⊛ : ∀ {i} (ρ : Env i) (n : ℤ) (a : Linear i) → [ ρ /x] (n ⊛ a) ≡ n * ([ ρ /x] a)
[ [] /x]-⊛ n ([] ∷+ k) = refl
[ x ∷ ρ /x]-⊛ n ((c ∷ cs) ∷+ k)
  rewrite [ ρ /x]-⊛ n (cs ∷+ k) = begin
  n * c * x + n * [ ρ /x] (cs ∷+ k)
    ≡⟨ cong (λ ● → ● + _) (IntProp.*-assoc n c x) ⟩
  n * (c * x) + n * [ ρ /x] (cs ∷+ k)
    ≡⟨ cong (λ ● → ● + _) (IntProp.*-comm n (c * x)) ⟩
  c * x * n + n * [ ρ /x] (cs ∷+ k)
    ≡⟨ cong (λ ● → c * x * n + ●) (IntProp.*-comm n _) ⟩
  c * x * n + [ ρ /x] (cs ∷+ k) * n
    ≡⟨ sym (IntProp.*-distribʳ-+ n (c * x) _) ⟩
  (c * x + [ ρ /x] (cs ∷+ k)) * n
    ≡⟨ sym (IntProp.*-comm n _) ⟩
  n * (c * x + [ ρ /x] (cs ∷+ k))
    ∎
  where open ≡-Reasoning

[_/x]-⊝ : ∀ {i} (ρ : Env i) (a : Linear i)
         → [ ρ /x] (⊝ a) ≡ - [ ρ /x] a
[_/x]-⊝ [] ([] ∷+ k) = refl
[_/x]-⊝ (x ∷ ρ) (c x+ cs +ℤ k) = begin
  (- c) * x + [ ρ /x] (Vec.map -_ cs ∷+ (- k))
    ≡⟨ cong (λ ● → (- c) * x + ●) ([ ρ /x]-⊝ (cs ∷+ k)) ⟩
  (- c) * x + (- [ ρ /x] (cs ∷+ k))
    ≡⟨ cong (λ ● → ● * x + _) (sym (IntProp.-1*n≡-n c)) ⟩
  (- + 1) * c * x + (- [ ρ /x] (cs ∷+ k))
    ≡⟨ cong (λ ● → ● + _) (IntProp.*-assoc (- + 1) c x) ⟩
  (- + 1) * (c * x) + (- [ ρ /x] (cs ∷+ k))
    ≡⟨ cong (λ ● → ● + _) (IntProp.-1*n≡-n (c * x)) ⟩
  (- (c * x) + - [ ρ /x] (cs ∷+ k))
    ≡⟨ sym (IntProp.neg-distrib-+ (c * x) _) ⟩
  - (c * x + [ ρ /x] (cs ∷+ k))
    ∎

  where open ≡-Reasoning

⊨[_/x]-trans : ∀ {i} (ρ : Env i) (a b c : Linear i)
              → ⊨[ ρ /x] (b ⊝ a)
              → ⊨[ ρ /x] (c ⊝ b)
              → ⊨[ ρ /x] (c ⊝ a)
⊨[ ρ /x]-trans a b c ⊨b⊝a ⊨c⊝b
  rewrite
    [ ρ /x]-⊕ b (⊝ a)
  | [ ρ /x]-⊕ c (⊝ b)
  | [ ρ /x]-⊕ c (⊝ a)
  | x≤y+z≡x-z≤y (+ 0) ([ ρ /x] b) ([ ρ /x] (⊝ a))
  | x≤y+z≡x-z≤y (+ 0) ([ ρ /x] c) ([ ρ /x] (⊝ b))
  | x≤y+z≡x-z≤y (+ 0) ([ ρ /x] c) ([ ρ /x] (⊝ a))
  | [ ρ /x]-⊝ a
  | [ ρ /x]-⊝ b
  | IntProp.neg-involutive ([ ρ /x] a)
  | IntProp.neg-involutive ([ ρ /x] b)
  | IntProp.+-identityˡ ([ ρ /x] a)
  | IntProp.+-identityˡ ([ ρ /x] b)
  = IntProp.≤-trans ⊨b⊝a ⊨c⊝b

[_/x]-# : ∀ {i} (ρ : Env i) (k : ℤ) → [ ρ /x] (# k) ≡ k
[ [] /x]-# k = refl
[ x ∷ ρ /x]-# k rewrite [ ρ /x]-# k = IntProp.+-identityˡ k

⊝#n≡#-n : ∀ {i} → (n : ℤ) → ⊝_ {i} (# n) ≡ # (- n)
⊝#n≡#-n {i} n rewrite VecProp.map-replicate -_ (+ 0) i = refl

⊨cs≡⊨0∷cs : ∀ {i} (x : ℤ) (ρ : Env i) (ir : Σ (Linear (suc i)) Irrelevant)
           → (⊨[ ρ /x] ∘ tail ∘ proj₁) ir ≡ ⊨[ x ∷ ρ /x]ᵢ ir

⊨cs≡⊨0∷cs x ρ (c x+ cs +ℤ k , 0=c) = begin
  ⊨[ ρ /x] (cs ∷+ k)
    ≡⟨ cong (λ ● → + 0 ≤ ●) (sym (IntProp.+-identityˡ ([ ρ /x] (cs ∷+ k)))) ⟩
  + 0 ≤ (+ 0) + [ ρ /x] (cs ∷+ k)
    ≡⟨ cong (λ ● → + 0 ≤ ● + [ ρ /x] (cs ∷+ k)) (sym (IntProp.*-zeroˡ x)) ⟩
  + 0 ≤ (+ 0) * x + [ ρ /x] (cs ∷+ k)
    ≡⟨ cong (λ ● → + 0 ≤ ● * x + _) 0=c ⟩
  + 0 ≤ c * x + [ ρ /x] (cs ∷+ k)
    ≡⟨⟩
  + 0 ≤ [ x ∷ ρ /x] (c x+ cs +ℤ k)
    ≡⟨⟩
  ⊨[ x ∷ ρ /x]ᵢ (c x+ cs +ℤ k , 0=c)
    ∎
  where open ≡-Reasoning

⊝⊝a≡a : ∀ {i} (a : Linear i) → ⊝ (⊝ a) ≡ a
⊝⊝a≡a (cs ∷+ k) = begin
  (Vec.map -_ (Vec.map -_ cs)) ∷+ (- (- k))
    ≡⟨ cong (_ ∷+_) (IntProp.neg-involutive k) ⟩
  (Vec.map -_ (Vec.map -_ cs)) ∷+ k
    ≡⟨ cong (_∷+ k) (sym (VecProp.map-∘ -_ -_ cs)) ⟩
  (Vec.map (-_ ∘ -_) cs) ∷+ k
    ≡⟨ cong (_∷+ k) (VecProp.map-cong IntProp.neg-involutive cs) ⟩
  (Vec.map id cs) ∷+ k
    ≡⟨ cong (_∷+ k) (VecProp.map-id cs) ⟩
  cs ∷+ k
    ∎
  where open ≡-Reasoning

-- div requires an implicit proof showing its divisor is non-zero
a/α : ∀ {i} → Env i → Σ (Linear (suc i)) LowerBound → ℤ
a/α ρ ((+_ zero x+ cs +ℤ k) , +<+ ())
a/α ρ ((+[1+ n ] x+ cs +ℤ k) , +<+ (Nat.s≤s Nat.z≤n)) = let a = - [ ρ /x] (cs ∷+ k) in sign a ◃ (∣ a ∣ div suc n)

b/β : ∀ {i} → Env i → Σ (Linear (suc i)) UpperBound → ℤ
b/β ρ ((-[1+ n ] x+ cs +ℤ k) , -<+) = let b = [ ρ /x] (cs ∷+ k) in sign b ◃ (∣ b ∣ div suc n)

α≡1∨-β≡-1 : ∀ {i} (lu : Pair (suc i)) → Set
α≡1∨-β≡-1 lu = head (proj₁ (proj₁ lu)) ≡ + 1 ⊎ head (proj₁ (proj₂ lu)) ≡ - + 1

α≡1∨-β≡-1? : ∀ {i} → Decidable {A = Pair (suc i)} α≡1∨-β≡-1
α≡1∨-β≡-1? ((l , _) , (u , _)) with head l ≟ + 1 | head u ≟ - + 1
... | no ¬α≡1 | no ¬-β≡-1 = no λ { (inj₁ α≡1) → ¬α≡1 α≡1 ; (inj₂ -β≡-1) → ¬-β≡-1 -β≡-1}
... | yes α≡1 | _         = yes (inj₁ α≡1)
... | _       | yes -β≡-1 = yes (inj₂ -β≡-1)
\end{code}

\begin{code}
---------------------
-- Norrish's proof

\end{code}
%<*norrish-inner-header>
\begin{code}
module Norrish {i : ℕ} (ρ : Env i) (lu : Pair (suc i)) where
  l = proj₁ lu
  u = proj₂ lu
  α = head (proj₁ l)
  -a = tail (proj₁ l)
  a = ⊝ -a
  0<α = proj₂ l
  -β = head (proj₁ u)
  β = - -β
  b = tail (proj₁ u)
  0>-β = proj₂ u
  0<β : + 0 < β
  0<β with -β | 0>-β
  0<β | +_ n | +<+ ()
  0<β | -[1+ n ] | -<+ = +<+ (Nat.s≤s Nat.z≤n)
  n = a/α ρ l
\end{code}
%</norrish-inner-header>

%<*goal-example>
\begin{code}
  aβ≤αb : Linear i
  aβ≤αb = ((α ⊛ b) ⊝ (β ⊛ a))
\end{code}
%</goal-example>

\begin{code}
  [α-1][β-1] : ℤ
  [α-1][β-1] = (α - + 1) * (β - + 1)

  ⊨0≤[α-1][β-1] : (+ 0) ≤ [α-1][β-1]
  ⊨0≤[α-1][β-1] with α | 0<α
  ⊨0≤[α-1][β-1] | + (suc n) | +<+ (Nat.s≤s Nat.z≤n) with β | 0<β
  ⊨0≤[α-1][β-1] | + (suc n) | +<+ (Nat.s≤s Nat.z≤n) | + (suc m) | +<+ (Nat.s≤s Nat.z≤n) rewrite IntProp.+◃n≡+n (n Nat.* m) = +≤+ Nat.z≤n

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
  αb-aβ<[α-1][β-1] = (# [α-1][β-1]) ⊝ aβ≤αb ⊝ (# (+ 1))

  α≡1∨-β≡-1→[α-1][β-1]≡0 : (α ≡ + 1 ⊎ -β ≡ - + 1) → [α-1][β-1] ≡ + 0
  α≡1∨-β≡-1→[α-1][β-1]≡0 (inj₁ α≡1) rewrite α≡1 = refl
  α≡1∨-β≡-1→[α-1][β-1]≡0 (inj₂ -β≡-1) rewrite -β≡-1 | IntProp.*-zeroʳ (α - + 1) = refl

  a≤αx⇒aβ≤αβx : (x : ℤ)
              → ⊨[ x ∷ ρ /x] (α x+ -a)
              → ⊨[ ρ /x] ((# (α * β * x)) ⊝ (β ⊛ a))
  a≤αx⇒aβ≤αβx x ⊨a≤αx with β | 0<β
  a≤αx⇒aβ≤αβx x ⊨a≤αx | + (suc n) | +<+ (Nat.s≤s m<n) = begin
    + 0
      ≡⟨ sym (IntProp.*-zeroˡ (+ suc n)) ⟩
    (+ 0) * (+ suc n)
      ≤⟨ IntProp.*-monoʳ-≤-pos n ⊨a≤αx ⟩
    ([ x ∷ ρ /x] (α x+ -a)) * (+ suc n)
      ≡⟨ cong (λ ● → (α * x + [ ρ /x] ●) * (+ suc n)) (sym (⊝⊝a≡a -a)) ⟩
    (α * x + [ ρ /x] (⊝ a)) * (+ suc n)
      ≡⟨ cong (λ ● → (α * x + ●) * (+ suc n)) ([ ρ /x]-⊝ a) ⟩
    (α * x + - [ ρ /x] a) * (+ suc n)
      ≡⟨ IntProp.*-distribʳ-+ (+ suc n) (α * x) (- [ ρ /x] a) ⟩
    α * x * (+ suc n) + (- [ ρ /x] a) * (+ suc n)
      ≡⟨ cong  (λ ● → α * x * (+ suc n) + ● * (+ suc n)) (sym (IntProp.-1*n≡-n ([ ρ /x] a))) ⟩
    α * x * (+ suc n) + (- + 1) * ([ ρ /x] a) * (+ suc n)
      ≡⟨ cong (λ ● → α * x * (+ suc n) + ●) (IntProp.*-assoc (- + 1) ([ ρ /x] a) (+ suc n)) ⟩
    α * x * (+ suc n) + (- + 1) * (([ ρ /x] a) * (+ suc n))
      ≡⟨ cong (λ ● → α * x * (+ suc n) + ●) (IntProp.-1*n≡-n (([ ρ /x] a) * (+ suc n))) ⟩
    α * x * (+ suc n) + - (([ ρ /x] a) * (+ suc n))
      ≡⟨ cong (λ ● → α * x * (+ suc n) + - ●) (IntProp.*-comm ([ ρ /x] a) (+ suc n)) ⟩
    α * x * (+ suc n) + - ((+ suc n) * ([ ρ /x] a))
      ≡⟨ cong (λ ● → α * x * (+ suc n) + - ●) (sym ([ ρ /x]-⊛ (+ suc n) a)) ⟩
    α * x * (+ suc n) + - [ ρ /x] ((+ suc n) ⊛ a)
      ≡⟨ cong (λ ● → ● * (+ suc n) + _) (IntProp.*-comm α x) ⟩
    x * α * (+ suc n) + - [ ρ /x] ((+ suc n) ⊛ a)
      ≡⟨ cong (λ ● → ● + _) (IntProp.*-assoc x α (+ suc n)) ⟩
    x * (α * (+ suc n)) + - [ ρ /x] ((+ suc n) ⊛ a)
      ≡⟨ cong (λ ● → ● + _) (IntProp.*-comm x (α * (+ suc n))) ⟩
    α * (+ suc n) * x + - [ ρ /x] ((+ suc n) ⊛ a)
      ≡⟨ cong (λ ● → α * (+ suc n) * x + ●) (sym ([ ρ /x]-⊝ ((+ suc n) ⊛ a))) ⟩
    α * (+ suc n) * x + [ ρ /x] ⊝ ((+ suc n) ⊛ a)
      ≡⟨ cong (λ ● → ● + _) (sym ([ ρ /x]-# (α * (+ suc n) * x))) ⟩
    [ ρ /x] (# (α * (+ suc n) * x)) + [ ρ /x] ⊝ ((+ suc n) ⊛ a)
      ≡⟨ sym ([ ρ /x]-⊕ _ _) ⟩
    [ ρ /x] ((# (α * (+ suc n) * x)) ⊝ ((+ suc n) ⊛ a))
      ∎
    where open ≤-Reasoning

  -- Similar to above's
  postulate βx≤b⇒αβx≤αb : (x : ℤ)
                        → ⊨[ x ∷ ρ /x] (-β x+ b)
                        → ⊨[ ρ /x] ((α ⊛ b) ⊝ (# (α * β * x)))
\end{code}

%<*real-shadow>
\begin{code}
  ⊨real-shadow : (x : ℤ) → (α ≡ + 1 ⊎ -β ≡ - + 1)
               → ⊨[ x ∷ ρ /x] (α x+ -a)
               → ⊨[ x ∷ ρ /x] (-β x+ b)
               → ⊨[ ρ /x] (aβ≤αb ⊝ (# [α-1][β-1]))
  ⊨real-shadow x α≡1∨-β≡-1 a≤αx βx≤b = begin
    + 0
      ≤⟨ ⊨[ ρ /x]-trans (β ⊛ a) (# (α * β * x)) (α ⊛ b)
         (a≤αx⇒aβ≤αβx x a≤αx ) (βx≤b⇒αβx≤αb x βx≤b) ⟩
    [ ρ /x] aβ≤αb
      ≡⟨ sym (IntProp.+-identityʳ _) ⟩
    [ ρ /x] aβ≤αb + (+ 0)
      ≡⟨ cong (λ ● → [ ρ /x] aβ≤αb + ●) (sym ([ ρ /x]-# (+ 0))) ⟩
    [ ρ /x] aβ≤αb + [ ρ /x] (# (+ 0))
      ≡⟨ sym ([ ρ /x]-⊕ aβ≤αb (# (+ 0))) ⟩
    [ ρ /x] (aβ≤αb ⊕ (# (+ 0)))
      ≡⟨ cong (λ ● → [ ρ /x] (aβ≤αb ⊕ ●)) (sym (⊝#n≡#-n (+ 0))) ⟩
    [ ρ /x] (aβ≤αb ⊝ (# (+ 0)))
      ≡⟨ cong (λ ● → [ ρ /x] (aβ≤αb ⊝ (# ●))) (sym (α≡1∨-β≡-1→[α-1][β-1]≡0 α≡1∨-β≡-1)) ⟩
    [ ρ /x] (aβ≤αb ⊝ (# [α-1][β-1]))
      ∎
    where open ≤-Reasoning
\end{code}
%</real-shadow>

%<*example-subgoal>
\begin{code}
  ⊨βa≤αb : ⊨[ ρ /x] (aβ≤αb ⊝ (# [α-1][β-1])) → ⊨[ ρ /x] aβ≤αb
  ⊨βa≤αb ⊨ds = begin
    + 0
      ≤⟨ ⊨ds ⟩
    [ ρ /x] (aβ≤αb ⊝ (# [α-1][β-1]))
      ≡⟨ cong (λ ● → [ ρ /x] (aβ≤αb ⊕ ●)) (⊝#n≡#-n [α-1][β-1]) ⟩
    [ ρ /x] (aβ≤αb ⊕ (# (- [α-1][β-1])))
      ≡⟨ [ ρ /x]-⊕ _ _ ⟩
    [ ρ /x] aβ≤αb + [ ρ /x] (# (- [α-1][β-1]))
      ≡⟨ cong (λ ● → [ ρ /x] aβ≤αb + ●) ([ ρ /x]-# _) ⟩
    [ ρ /x] aβ≤αb - [α-1][β-1]
      ≤⟨ 0≤n→m-n≤m _ _ ⊨0≤[α-1][β-1]  ⟩
    [ ρ /x] aβ≤αb
      ∎
    where open ≤-Reasoning
\end{code}
%</example-subgoal>

\begin{code}
  postulate ⊨αβn<aβ≤αb<αβ[n+1] : {xs : List ℤ}
                               → ⊨[ ρ /x] aβ≤αb
                               → ¬ (∃[ xs ] (λ x → ⊨[ x ∷ ρ /x]ₚ lu))
                               → ∀[ αβn<aβ≤αb<αβ[n+1] ] ⊨[ ρ /x]

  postulate ⊨α≤αβ[n+1]-αb : ∀[ αβn<aβ≤αb<αβ[n+1] ] ⊨[ ρ /x]
                          → ⊨[ ρ /x] α≤αβ[n+1]-αb

  postulate ⊨β≤aβ-αβn : ∀[ αβn<aβ≤αb<αβ[n+1] ] ⊨[ ρ /x]
                      → ⊨[ ρ /x] β≤aβ-αβn

  postulate ⊭[α-1][β-1]≤αb-aβ : ⊨[ ρ /x] α≤αβ[n+1]-αb
                              → ⊨[ ρ /x] β≤aβ-αβn
                              → ⊨[ ρ /x] (aβ≤αb ⊝ (# [α-1][β-1]))
                              → ⊥
\end{code}

%<*norrish-type>
\begin{code}
⊨norrish : ∀ {i} (ρ : Env i) (xs : List ℤ) (lu : Pair (suc i))
         → ¬ ∃[ xs ] (λ x → ⊨[ x ∷ ρ /x]ₚ lu)
         → ¬ ⊨[ ρ /x] (lu ↓ₚ)
\end{code}
%</norrish-type>

%<*norrish>
\begin{code}
⊨norrish ρ xs lu ⊭xs ⊨lu↓ =
  let ps = ⊨αβn<aβ≤αb<αβ[n+1] (⊨βa≤αb ⊨lu↓ ) ⊭xs
   in ⊭[α-1][β-1]≤αb-aβ (⊨α≤αβ[n+1]-αb ps) (⊨β≤aβ-αβn ps) ⊨lu↓
  where open Norrish ρ lu
\end{code}
%</norrish>

\begin{code}
-----------------------------
-- Bounded search for an x

\end{code}
%<*search-space>
\begin{code}
start : ∀ {i} → Env i → List (Σ (Linear (suc i)) LowerBound) → ℤ
start ρ ls = List.foldr _⊔_ (+ 0) (map (a/α ρ) ls)

stop : ∀ {i} → Env i → List (Σ (Linear (suc i)) UpperBound) → ℤ
stop ρ us = List.foldr _⊓_ (+ 0) (map (b/β ρ) us)

search-space : ∀ {i} → Env i → List (Pair (suc i)) → List ℤ
search-space ρ lus with start ρ (map proj₁ lus)
search-space ρ lus | Δ₀ with stop ρ (map proj₂ lus) - Δ₀
search-space ρ lus | Δ₀ | + n = List.applyUpTo (λ i → + i + Δ₀) n
search-space ρ lus | Δ₀ | -[1+ n ] = []
\end{code}
%</search-space>

%<*by-contradiction-type>
\begin{code}
by-contradiction : ∀ {i} (ρ : Env i) (xs : List ℤ) (lus : List (Pair (suc i)))
                 → ∀[ map _↓ₚ lus ] ⊨[ ρ /x]
                 → ¬ ∀[ xs ] (λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
\end{code}
%</by-contradiction-type>

%<*by-contradiction>
\begin{code}
by-contradiction {i} ρ xs lus ⊨lus↓ ∀xs¬∀lus =
  ¬∃lus¬∃xs lus ⊨lus↓ (∀xs¬∀lus⇒∃lus¬∃xs ∀xs¬∀lus)
\end{code}
%</by-contradiction>

\begin{code}
  where
\end{code}

%<*contradiction-search>
\begin{code}
  ¬∃lus¬∃xs : (lus : List (Pair (suc i)))
             → ∀[ map _↓ₚ lus ] ⊨[ ρ /x]
             → ∃[ lus ] (λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
             → ⊥

  ¬∃lus¬∃xs [] [] ()
  ¬∃lus¬∃xs (lu ∷ lus) (⊨lu↓ ∷ ⊨lus↓) (here ¬∃xs)       = ⊨norrish ρ xs lu ¬∃xs ⊨lu↓
  ¬∃lus¬∃xs (lu ∷ lus) (⊨lu↓ ∷ ⊨lus↓) (there ∃lus¬∃xs) = ¬∃lus¬∃xs lus ⊨lus↓ ∃lus¬∃xs
\end{code}
%</contradiction-search>

%<*contradiction-adaptation>
\begin{code}
  postulate ∀lus∃xs⇒∃xs∀lus : ∀[ lus ] (λ lu → ∃[ xs ] (λ x → ⊨[ x ∷ ρ /x]ₚ lu))
                            → ∃[ xs ] (λ x → ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)

  ∀xs¬∀lus⇒∃lus¬∃xs : ∀[ xs ] (λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
                      → ∃[ lus ] (λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)

  ∀xs¬∀lus⇒∃lus¬∃xs = begin
    ∀[ xs ] (λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
      ∼⟨ AllProp.All¬⇒¬Any ⟩
    ¬ ∃[ xs ] (λ x → ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
      ∼⟨ (λ ¬∃xs∀lus ∀lus∃xs → ¬∃xs∀lus (∀lus∃xs⇒∃xs∀lus ∀lus∃xs)) ⟩
    ¬ ∀[ lus ] (λ lu → ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
      ∼⟨ AllProp.¬All⇒Any¬ (λ lu → any (λ x → ⊨? lu [ x ∷ ρ /x]ₚ) xs) lus ⟩
    ∃[ lus ] (λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
      ∎
    where open ⇒-Reasoning
\end{code}
%</contradiction-adaptation>

\begin{code}
--------------------------------------------------------------------
-- Proofs of correctness in both directions, for pairs and irrels
\end{code}

%<*find-x>
\begin{code}
⊨↑ₚ : ∀ {i} (ρ : Env i) (lus : List (Pair (suc i)))
       → ∀[ map _↓ₚ lus ] ⊨[ ρ /x]
       → Σ ℤ λ x → ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ

⊨↑ₚ ρ lus ⊨lus↓ with search-space ρ lus
⊨↑ₚ ρ lus ⊨lus↓ | xs = search (λ x → all ⊨?_[ x ∷ ρ /x]ₚ lus ) xs (by-contradiction ρ xs lus ⊨lus↓)
\end{code}
%</find-x>

\begin{code}
⊨↓ₚ : ∀ {i} (x : ℤ) (ρ : Env i) (lus : List (Pair (suc i)))
      → ∀[ lus ] α≡1∨-β≡-1
      → ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ
      → ∀[ map _↓ₚ lus ] ⊨[ ρ /x]
⊨↓ₚ x ρ [] [] [] = []
⊨↓ₚ x ρ (lu@(((_ x+ _ +ℤ _) , _) , ((_ x+ _ +ℤ _) , _)) ∷ lus) (t ∷ ts) ((⊨l , ⊨u) ∷ ⊨lus) =
  Norrish.⊨real-shadow ρ lu x t ⊨l ⊨u ∷ (⊨↓ₚ x ρ lus ts ⊨lus)

⊨↑ᵢ : ∀ {i} (x : ℤ) (ρ : Env i) (irs : List (Σ (Linear (suc i)) Irrelevant))
    → ∀[ map _↓ᵢ irs ] ⊨[ ρ /x]
    → ∀[ irs ] ⊨[ x ∷ ρ /x]ᵢ

⊨↑ᵢ x ρ [] [] = []
⊨↑ᵢ x ρ (ir ∷ irs) (⊨ir↓ ∷ ⊨irs↓) rewrite ⊨cs≡⊨0∷cs x ρ ir = ⊨ir↓ ∷ (⊨↑ᵢ x ρ irs ⊨irs↓)

⊨↓ᵢ : ∀ {i} (x : ℤ) (ρ : Env i) (irs : List (Σ (Linear (suc i)) Irrelevant))
    → ∀[ irs ] ⊨[ x ∷ ρ /x]ᵢ
    → ∀[ map _↓ᵢ irs ] ⊨[ ρ /x]

⊨↓ᵢ x ρ [] [] = []
⊨↓ᵢ x ρ (ir ∷ irs) (⊨ir ∷ ⊨irs) rewrite sym (⊨cs≡⊨0∷cs x ρ ir) = ⊨ir ∷ (⊨↓ᵢ x ρ irs ⊨irs)
\end{code}

\begin{code}
------------------------------------------
-- Evaluation

\end{code}

%<*result>
\begin{code}
data Result : Set where
  satisfiable unsatisfiable undecided : Result
\end{code}
%</result>

%<*elimination>
\begin{code}
Ω : ∀ {i} → List (Linear i) → Result
Ω {zero}  as with all ⊨?_[ [] /x] as
Ω {zero}  as | yes _ = satisfiable
Ω {zero}  as | no _  = unsatisfiable
Ω {suc i} as with Ω (as ↓)
Ω {suc i} as | unsatisfiable with all α≡1∨-β≡-1? (pairs as)
Ω {suc i} as | unsatisfiable | yes _ = unsatisfiable
Ω {suc i} as | unsatisfiable | no _  = undecided
Ω {suc i} as | r                     = r
\end{code}
%</elimination>

\begin{code}
---------------------------------
-- Proofs of correctness
\end{code}

%<*correctness>
\begin{code}
Ω-Sound : ∀ {i} (as : List (Linear i)) → Set
Ω-Sound as with Ω as
Ω-Sound as | undecided      = ⊤
Ω-Sound as | satisfiable    = ⊨ as
Ω-Sound as | unsatisfiable  = ⊨ as → ⊥
\end{code}
%</correctness>

\begin{code}
-- Unproven utils, for mixing evidence together and taking it appart
postulate entangle : ∀ {i} {P : Linear (suc i) → Set} (as : List (Linear (suc i)))
                   → ∀[ irrels as ] (λ i → P (proj₁ i))
                   → ∀[ pairs as ] (λ lu → P (proj₁ (proj₁ lu)) × P (proj₁ (proj₂ lu)))
                   → ∀[ as ] P

postulate untangleᵢ : ∀ {i} {P : Linear (suc i) → Set} (as : List (Linear (suc i)))
                   → ∀[ as ] P
                   → ∀[ irrels as ] (λ i → P (proj₁ i))

postulate untangleₚ : ∀ {i} {P : Linear (suc i) → Set} (as : List (Linear (suc i)))
                   → ∀[ as ] P
                   → ∀[ pairs as ] (λ lu → P (proj₁ (proj₁ lu)) × P (proj₁ (proj₂ lu)))
\end{code}

\begin{code}
-- Our verdicts are sound

unsat : ∀ {i} (as : List (Linear i)) → Ω as ≡ unsatisfiable → ⊨ as → ⊥
unsat {zero} as ep with all ⊨?_[ [] /x] as
unsat {zero} as () | yes p
unsat {zero} as ep | no ¬p = λ {([] , ⊨as) → ¬p ⊨as}
unsat {suc i} as ep with Ω (as ↓)   | inspect Ω (as ↓)
unsat {suc i} as () | undecided     | _
unsat {suc i} as () | satisfiable   | _
unsat {suc i} as ep | unsatisfiable | _        with all α≡1∨-β≡-1? (pairs as)
unsat {suc i} as () | unsatisfiable | _        | no ¬∀α≡1∨-β≡-1
unsat {suc i} as ep | unsatisfiable | >[ eq ]< | yes ∀α≡1∨-β≡-1 with unsat (as ↓) eq
unsat {suc i} as ep | unsatisfiable | >[ eq ]< | yes ∀α≡1∨-β≡-1 | ⊨as↓→⊥ = λ {
  (x ∷ ρ , ⊨as) → ⊨as↓→⊥ (ρ , AllProp.++⁺
    (⊨↓ᵢ x ρ (irrels as)           (untangleᵢ as ⊨as))
    (⊨↓ₚ x ρ (pairs as) ∀α≡1∨-β≡-1 (untangleₚ as ⊨as)))}

sat : ∀ {i} (as : List (Linear i)) → Ω as ≡ satisfiable → ⊨ as
sat {zero} as ep with all ⊨?_[ [] /x] as
sat {zero} as ep | yes p = [] , p
sat {zero} as () | no ¬p
sat {suc i} as ep with Ω (as ↓)   | inspect Ω (as ↓)
sat {suc i} as () | undecided     | _
sat {suc i} as ep | unsatisfiable | _ with all α≡1∨-β≡-1? (pairs as)
sat {suc i} as () | unsatisfiable | _ | yes _
sat {suc i} as () | unsatisfiable | _ | no _
sat {suc i} as ep | satisfiable   | >[ eq ]< with sat (as ↓) eq
sat {suc i} as ep | _ | _ | ρ , ⊨as↓ with AllProp.++⁻ (map _↓ᵢ (irrels as)) ⊨as↓
sat {suc i} as ep | _ | _ | ρ , ⊨as↓ | ⊨irs↓ , ⊨lus↓ with ⊨↑ₚ ρ (pairs as) ⊨lus↓
sat {suc i} as ep | _ | _ | ρ , ⊨as↓ | ⊨irs↓ , ⊨lus↓ | x , ⊨lus with ⊨↑ᵢ x ρ (irrels as) ⊨irs↓
sat {suc i} as ep | _ | _ | ρ , ⊨as↓ | ⊨irs↓ , ⊨lus↓ | x , ⊨lus | ⊨irs = (x ∷ ρ) , (entangle as ⊨irs ⊨lus)
\end{code}

%<*correct>
\begin{code}
Ω-sound : ∀ {i} (as : List (Linear i)) → Ω-Sound as
Ω-sound as with Ω as       | inspect Ω as
Ω-sound as | undecided     | _        = tt
Ω-sound as | unsatisfiable | >[ eq ]< = unsat as eq
Ω-sound as | satisfiable   | >[ eq ]< = sat as eq
\end{code}
%</correct>
