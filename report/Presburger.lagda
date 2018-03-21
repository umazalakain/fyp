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
module ⇒-Reasoning = PRE (preorder implication lzero)
open Function.Related using (≡⇒) 

import Relation.Binary.PartialOrderReasoning as POR
module ≤-Reasoning = POR IntProp.≤-poset renaming (_≈⟨_⟩_ to _≡⟨_⟩_ ; _≈⟨⟩_ to _≡⟨⟩_)
module ≡-Reasoning = Relation.Binary.PropositionalEquality.≡-Reasoning

∀[_]_ : ∀ {a p} {A : Set a} → List A → (A → Set p) → Set (p ℓ⊔ a)
∀[ xs ] P = All P xs 

∃[_]_ : ∀ {a p} {A : Set a} → List A → (A → Set p) → Set (p ℓ⊔ a)
∃[ xs ] P = Any P xs 

×-list-inner : {X Y : Set} → List X → Y → List (X × Y)
×-list-inner [] y = []
×-list-inner (x ∷ xs) y = (x , y) ∷ ×-list-inner xs y

×-list : {X Y : Set} → List X → List Y → List (X × Y)
×-list xs [] = []
×-list xs (y ∷ ys) = ×-list-inner xs y ++ ×-list xs ys
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
\end{code}

%<*constraint>
\begin{code}
Constraint : (i : ℕ) (P : Linear i → Set) → Set
Constraint i P = Σ (Linear i) P
\end{code}
%</constraint>

%<*pair>
\begin{code}
Pair : (i : ℕ) → Set
Pair i = Constraint i LowerBound × Constraint i UpperBound
\end{code}
%</pair>

\begin{code}
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

%<*evaluation
\begin{code}
Env : ℕ → Set
Env i = Vec ℤ i

[_/x]_ : ∀ {i} → Env i → Linear i → ℤ
[_/x]_ [] ([] ∷+ k) = k
[_/x]_ (x ∷ xs) ((c ∷ cs) ∷+ k) = c * x + [ xs /x] (cs ∷+ k)

-- div requires an implicit proof showing its divisor is non-zero
a/α : ∀ {i} → Env i → Constraint (suc i) LowerBound → ℤ
a/α ρ (+_ zero x+ -cs +ℤ -k , (_≤_.+≤+ ()))
a/α ρ (+_ (suc α-1) x+ -cs +ℤ -k , lb) = let a = - [ ρ /x] (-cs ∷+ -k) in sign a ◃ (∣ a ∣ div suc α-1)
a/α ρ (-[1+ n ] x+ -cs +ℤ -k , ())

b/β : ∀ {i} → Env i → Constraint (suc i) UpperBound → ℤ
b/β ρ (+_ c x+ cs +ℤ k , _≤_.+≤+ ())
b/β ρ (-[1+ β-1 ] x+ cs +ℤ k , ub) = let b = [ ρ /x] (cs ∷+ k) in sign b ◃ (∣ b ∣ div suc β-1)
\end{code}
%</evaluation>

%<*meaning>
\begin{code}
⊨[_/x] : ∀ {i} → Env i → Linear i → Set
⊨[ ρ /x] a = + 0 ≤ ([ ρ /x] a)
\end{code}
%</meaning>

\begin{code}
⊨[_/x]ₚ : ∀ {i} → Env i → Pair i → Set
⊨[ ρ /x]ₚ ((l , _) , (u , _)) = ⊨[ ρ /x] l × ⊨[ ρ /x] u

⊨[_/x]ᵢ : ∀ {i} → Env i → Constraint i Irrelevant → Set
⊨[ ρ /x]ᵢ (ir , _) = ⊨[ ρ /x] ir
\end{code}

%<*decidability>
\begin{code}
⟦_⟧[_/x] : ∀ {i} → (a : Linear i) → (ρ : Env i) → Dec (⊨[ ρ /x] a)
⟦ a ⟧[ ρ /x] = + 0 ≤? [ ρ /x] a

⟦_⟧[_/x]ₚ : ∀ {i} → (lu : Pair i) → (ρ : Env i) → Dec (⊨[ ρ /x]ₚ lu)
⟦ ((l , _) , (u , _)) ⟧[ ρ /x]ₚ with ⟦ l ⟧[ ρ /x] | ⟦ u ⟧[ ρ /x]
⟦ (l , _) , u , _ ⟧[ ρ /x]ₚ | yes pl | yes pu = yes (pl , pu)
⟦ (l , _) , u , _ ⟧[ ρ /x]ₚ | _      | no ¬pu = no λ {(_ , pu) → ¬pu pu}
⟦ (l , _) , u , _ ⟧[ ρ /x]ₚ | no ¬pl | _      = no λ {(pl , _) → ¬pl pl}
\end{code}
%</decidability>

%<*meaning-all>
\begin{code}
⊨ : ∀ {i} → List (Linear i) → Set
⊨ {i} as = Σ (Env i) λ ρ → All ⊨[ ρ /x] as
\end{code}
%</meaning-all>


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

[_/x]-+ : ∀ {i} (ρ : Env i) (a b : Linear i) → [ ρ /x] (a ⊕ b) ≡ [ ρ /x] a + [ ρ /x] b
[ [] /x]-+ ([] ∷+ ka) ([] ∷+ kb) = refl
[ x ∷ ρ /x]-+ ((ca ∷ csa) ∷+ ka) ((cb ∷ csb) ∷+ kb)
  rewrite [ ρ /x]-+ (csa ∷+ ka) (csb ∷+ kb) = begin 
  (ca + cb) * x + ([ ρ /x] (csa ∷+ ka) + [ ρ /x] (csb ∷+ kb))
    ≡⟨ cong (λ ⊚ → ⊚ + _) (IntProp.distribʳ x ca cb) ⟩
  (ca * x + cb * x) + ([ ρ /x] (csa ∷+ ka) + [ ρ /x] (csb ∷+ kb))
    ≡⟨ IntProp.+-assoc (ca * x) (cb * x) _ ⟩
  ca * x + (cb * x + ([ ρ /x] (csa ∷+ ka) + [ ρ /x] (csb ∷+ kb)))
    ≡⟨ cong (λ ⊚ → ca * x + ⊚) (sym (IntProp.+-assoc (cb * x) _ _)) ⟩
  ca * x + (cb * x + [ ρ /x] (csa ∷+ ka) + [ ρ /x] (csb ∷+ kb))
    ≡⟨ cong (λ ⊚ → ca * x + (⊚ + _)) (IntProp.+-comm (cb * x) ([ ρ /x] (csa ∷+ ka))) ⟩
  ca * x + ([ ρ /x] (csa ∷+ ka) + cb * x + [ ρ /x] (csb ∷+ kb))
    ≡⟨ cong (λ ⊚ → ca * x + ⊚) (IntProp.+-assoc ([ ρ /x] (csa ∷+ ka)) (cb * x) _) ⟩
  ca * x + ([ ρ /x] (csa ∷+ ka) + (cb * x + [ ρ /x] (csb ∷+ kb)))
    ≡⟨ sym (IntProp.+-assoc (ca * x) ([ ρ /x] (csa ∷+ ka)) _) ⟩
  (ca * x + [ ρ /x] (csa ∷+ ka)) + (cb * x + [ ρ /x] (csb ∷+ kb))
    ∎
  where open ≡-Reasoning

[_/x]-* : ∀ {i} (ρ : Env i) (n : ℤ) (a : Linear i) → [ ρ /x] (n ⊛ a) ≡ n * ([ ρ /x] a)
[ [] /x]-* n ([] ∷+ k) = refl
[ x ∷ ρ /x]-* n ((c ∷ cs) ∷+ k) rewrite [ ρ /x]-* n (cs ∷+ k) = begin
  n * c * x + n * [ ρ /x] (cs ∷+ k)
    ≡⟨ cong (λ ⊚ → ⊚ + _) (IntProp.*-assoc n c x) ⟩
  n * (c * x) + n * [ ρ /x] (cs ∷+ k)
    ≡⟨ cong (λ ⊚ → ⊚ + _) (IntProp.*-comm n (c * x)) ⟩
  c * x * n + n * [ ρ /x] (cs ∷+ k)
    ≡⟨ cong (λ ⊚ → c * x * n + ⊚) (IntProp.*-comm n _) ⟩
  c * x * n + [ ρ /x] (cs ∷+ k) * n
    ≡⟨ sym (IntProp.distribʳ n (c * x) _) ⟩
  (c * x + [ ρ /x] (cs ∷+ k)) * n
    ≡⟨ sym (IntProp.*-comm n _) ⟩
  n * (c * x + [ ρ /x] (cs ∷+ k))
    ∎
  where open ≡-Reasoning

⊨[_/x]-trans : ∀ {i} (ρ : Env i) (a b c : Linear i)
              → ⊨[ ρ /x] (b ⊝ a)
              → ⊨[ ρ /x] (c ⊝ b)
              → ⊨[ ρ /x] (c ⊝ a)
⊨[ ρ /x]-trans a b c ⊨b⊝a ⊨c⊝b with [ ρ /x] (b ⊝ a) | [ ρ /x] (c ⊝ b)
⊨[ ρ /x]-trans a b c ⊨b⊝a ⊨c⊝b | -[1+_] n | j = {!⊨b⊝a!}
⊨[ ρ /x]-trans a b c ⊨b⊝a ⊨c⊝b | +_ n | -[1+_] n₁ = {!!}
⊨[ ρ /x]-trans a b c ⊨b⊝a ⊨c⊝b | +_ n | +_ n₁ = {!!}
              
[_/x]-# : ∀ {i} (ρ : Env i) (k : ℤ) → [ ρ /x] (# k) ≡ k
[ [] /x]-# k = refl
[ x ∷ ρ /x]-# k rewrite [ ρ /x]-# k = IntProp.+-identityˡ k
  
⊝#n≡#-n : ∀ {i} → (n : ℤ) → ⊝_ {i} (# n) ≡ # (- n)
⊝#n≡#-n n = cong (_∷+ (- n)) (VecProp.map-replicate -_ (+ 0) _)

[_/x]#0≡0 : ∀ {i} (ρ : Env i) → [ ρ /x] (# (+ 0)) ≡ + 0
[ [] /x]#0≡0 = refl
[ x ∷ ρ /x]#0≡0 rewrite [ ρ /x]#0≡0 = refl

0≤n→m-n≤m : (m : ℤ) (n : ℤ) → (+ 0) ≤ n → m - n ≤ m
0≤n→m-n≤m m (-[1+_] n) ()
0≤n→m-n≤m (+_ m) (+_ n) 0≤n = {!!}
0≤n→m-n≤m (-[1+_] m) (+_ n) 0≤n = {!!}

⊨cs≡⊨0∷cs : ∀ {i} (ρ : Env i) (x : ℤ) (ir : Constraint (suc i) Irrelevant)
           → (⊨[ ρ /x] ∘ tail ∘ proj₁) ir ≡ ⊨[ x ∷ ρ /x]ᵢ ir

⊨cs≡⊨0∷cs ρ x (c x+ cs +ℤ k , 0=c) = begin 
  ⊨[ ρ /x] (cs ∷+ k)
    ≡⟨ cong (λ ⊚ → + 0 ≤ ⊚) (sym (IntProp.+-identityˡ ([ ρ /x] (cs ∷+ k)))) ⟩
  + 0 ≤ (+ 0) + [ ρ /x] (cs ∷+ k)
    ≡⟨ cong (λ ⊚ → + 0 ≤ ⊚ + [ ρ /x] (cs ∷+ k)) (sym (IntProp.*-zeroˡ x)) ⟩
  + 0 ≤ (+ 0) * x + [ ρ /x] (cs ∷+ k)
    ≡⟨ cong (λ ⊚ → + 0 ≤ ⊚ * x + _) 0=c ⟩
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
    ≡⟨ cong (_ ∷+_) (IntProp.doubleNeg k) ⟩
  (Vec.map -_ (Vec.map -_ cs)) ∷+ k
    ≡⟨ cong (_∷+ k) (sym (VecProp.map-∘ -_ -_ cs)) ⟩
  (Vec.map (-_ ∘ -_) cs) ∷+ k
    ≡⟨ cong (_∷+ k) (VecProp.map-cong IntProp.doubleNeg cs) ⟩
  (Vec.map id cs) ∷+ k
    ≡⟨ cong (_∷+ k) (VecProp.map-id cs) ⟩
  cs ∷+ k
    ∎
  where open ≡-Reasoning
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
  0<β | +_ _ | +≤+ ()
  0<β | -[1+_] n | z = +≤+ (Nat.s≤s Nat.z≤n)
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
  ⊨0≤[α-1][β-1] with α       | 0<α 
  ⊨0≤[α-1][β-1] | -[1+_] _   | ()
  ⊨0≤[α-1][β-1] | +_ zero    | +≤+ ()
  ⊨0≤[α-1][β-1] | +_ (suc n) | _ with β       | 0<β
  ⊨0≤[α-1][β-1] | +_ (suc n) | _ | -[1+_] m   | ()
  ⊨0≤[α-1][β-1] | +_ (suc n) | _ | +_ zero    | +≤+ ()
  ⊨0≤[α-1][β-1] | +_ (suc n) | _ | +_ (suc m) | _ rewrite IntProp.+◃n≡+n (n Nat.* m) = +≤+ Nat.z≤n
  
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
\end{code}

\begin{code}
  α≡1∨-β≡-1→[α-1][β-1]≡0 : (α ≡ + 1 ⊎ -β ≡ - + 1) → [α-1][β-1] ≡ + 0
  α≡1∨-β≡-1→[α-1][β-1]≡0 (inj₁ α≡1) rewrite α≡1 = refl
  α≡1∨-β≡-1→[α-1][β-1]≡0 (inj₂ -β≡-1) rewrite -β≡-1 | IntProp.*-zeroʳ (α - + 1) = refl
  
  a≤αx⇒aβ≤αβx : (x : ℤ)
              → ⊨[ x ∷ ρ /x] (α x+ -a)
              → ⊨[ ρ /x] ((# (α * β * x)) ⊝ (β ⊛ a))
  a≤αx⇒aβ≤αβx x ⊨a≤αx with β       | 0<β
  a≤αx⇒aβ≤αβx x ⊨a≤αx | -[1+_] n   | ()
  a≤αx⇒aβ≤αβx x ⊨a≤αx | +_ zero    | +≤+ ()
  a≤αx⇒aβ≤αβx x ⊨a≤αx | +_ (suc n) | z = begin
    + 0
      ≡⟨ sym (IntProp.*-zeroˡ (+ suc n)) ⟩
    (+ 0) * (+ suc n)
      ≤⟨ IntProp.*-+-right-mono n ⊨a≤αx ⟩
    ([ x ∷ ρ /x] (α x+ -a)) * (+ suc n)
      ≡⟨⟩
    (α * x + [ ρ /x] -a) * (+ suc n)
      ≡⟨ IntProp.distribʳ (+ suc n) (α * x) ([ ρ /x] -a) ⟩
    α * x * (+ suc n) + ([ ρ /x] -a) * (+ suc n)
      ≡⟨ cong (λ ⊚ → α * x * (+ suc n) + ⊚) (IntProp.*-comm ([ ρ /x] -a) (+ suc n)) ⟩
    α * x * (+ suc n) + (+ suc n) * ([ ρ /x] -a) 
      ≡⟨ cong (λ ⊚ → α * x * (+ suc n) + ⊚) (sym ([ ρ /x]-* (+ suc n) -a)) ⟩
    α * x * (+ suc n) + ([ ρ /x] ((+ suc n) ⊛ -a))
      ≡⟨ cong (λ ⊚ → ⊚ * (+ suc n) + _) (IntProp.*-comm α x) ⟩
    x * α * (+ suc n) + ([ ρ /x] ((+ suc n) ⊛ -a))
      ≡⟨ cong (λ ⊚ → ⊚ + _) (IntProp.*-assoc x α (+ suc n)) ⟩
    x * (α * (+ suc n)) + ([ ρ /x] ((+ suc n) ⊛ -a))
      ≡⟨ cong (λ ⊚ → ⊚ + _) (IntProp.*-comm x (α * (+ suc n))) ⟩
    (α * (+ suc n)) * x + ([ ρ /x] ((+ suc n) ⊛ -a))
      ≡⟨ {!!} ⟩
    [ ρ /x] ((# (α * (+ suc n) * x)) ⊝ ((+ suc n) ⊛ a))
      ∎
    where open ≤-Reasoning
              
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
      ≤⟨ ⊨[ ρ /x]-trans (β ⊛ a) (# (α * β * x)) (α ⊛ b) (a≤αx⇒aβ≤αβx x a≤αx ) (βx≤b⇒αβx≤αb x βx≤b) ⟩
    [ ρ /x] aβ≤αb
      ≡⟨ sym (IntProp.+-identityʳ _) ⟩
    [ ρ /x] aβ≤αb + (+ 0)
      ≡⟨ cong (λ ⊚ → [ ρ /x] aβ≤αb + ⊚) (sym [ ρ /x]#0≡0) ⟩
    [ ρ /x] aβ≤αb + [ ρ /x] (# (+ 0))
      ≡⟨ sym ([ ρ /x]-+ aβ≤αb (# (+ 0))) ⟩
    [ ρ /x] (aβ≤αb ⊕ (# (+ 0)))
      ≡⟨ cong (λ ⊚ → [ ρ /x] (aβ≤αb ⊕ ⊚)) (sym (⊝#n≡#-n (+ 0))) ⟩
    [ ρ /x] (aβ≤αb ⊝ (# (+ 0)))
      ≡⟨ cong (λ ⊚ → [ ρ /x] (aβ≤αb ⊝ (# ⊚))) (sym (α≡1∨-β≡-1→[α-1][β-1]≡0 α≡1∨-β≡-1)) ⟩
    [ ρ /x] (aβ≤αb ⊝ (# [α-1][β-1]))
      ∎
    where open ≤-Reasoning
\end{code}
%</real-shadow>

%<*norrish-subgoal-1>
\begin{code}
  ⊨βa≤αb : ⊨[ ρ /x] (aβ≤αb ⊝ (# [α-1][β-1])) → ⊨[ ρ /x] aβ≤αb
  ⊨βa≤αb ⊨ds = begin 
    + 0
      ≤⟨ ⊨ds ⟩
    [ ρ /x] (aβ≤αb ⊝ (# [α-1][β-1]))
      ≡⟨ cong (λ ⊚ → [ ρ /x] (aβ≤αb ⊕ ⊚)) (⊝#n≡#-n [α-1][β-1]) ⟩
    [ ρ /x] (aβ≤αb ⊕ (# (- [α-1][β-1])))
      ≡⟨ [ ρ /x]-+ _ _ ⟩
    [ ρ /x] aβ≤αb + [ ρ /x] (# (- [α-1][β-1]))
      ≡⟨ cong (λ ⊚ → [ ρ /x] aβ≤αb + ⊚) ([_/x]-# ρ _) ⟩
    [ ρ /x] aβ≤αb + (- [α-1][β-1])
      ≤⟨ 0≤n→m-n≤m _ _ ⊨0≤[α-1][β-1]  ⟩
    [ ρ /x] aβ≤αb
      ∎
    where open ≤-Reasoning
\end{code}
%</norrish-subgoal-1>

%<*norrish-subgoal-2>
\begin{code}
  ⊨αβn<aβ≤αb<αβ[n+1] : {xs : List ℤ}
                     → ⊨[ ρ /x] aβ≤αb
                     → ¬ (∃[ xs ] (λ x → ⊨[ x ∷ ρ /x]ₚ lu))
                     → All ⊨[ ρ /x] αβn<aβ≤αb<αβ[n+1]
\end{code}
%</norrish-subgoal-2>

\begin{code}
  ⊨αβn<aβ≤αb<αβ[n+1] ⊨p₁ ⊭p₂ = r₁ ∷ r₂ ∷ r₃ ∷ []
    where
      open ≤-Reasoning

      r₁ = begin
        + 0
          ≤⟨ {!!} ⟩
        [ ρ /x] ((β ⊛ a) ⊝ (# (α * β * n)) ⊝ (# (+ 1)))
          ∎
      r₂ = begin
        + 0
          ≤⟨ {!!} ⟩
        [ ρ /x] ((α ⊛ b) ⊝ (β ⊛ a))
          ∎
      r₃ = begin
        + 0
          ≤⟨ {!!} ⟩
        [ ρ /x] ((# (α * β * (n + + 1))) ⊝ (α ⊛ b) ⊝ (# (+ 1)))
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
    [ ρ /x] α≤αβ[n+1]-αb
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
    [ ρ /x] β≤aβ-αβn
      ∎
    where open ≤-Reasoning
\end{code}

%<*norrish-subgoal-5>
\begin{code}
  ⊭[α-1][β-1]≤αb-aβ : ⊨[ ρ /x] α≤αβ[n+1]-αb
                    → ⊨[ ρ /x] β≤aβ-αβn
                    → ⊨[ ρ /x] (aβ≤αb ⊝ (# [α-1][β-1]))
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

%<*norrish-type>
\begin{code}
⊨norrish : ∀ {i} (ρ : Env i) (xs : List ℤ) (lu : Pair (suc i))
         → ¬ ∃[ xs ] (λ x → ⊨[ x ∷ ρ /x]ₚ lu)
         → ¬ ⊨[ ρ /x] (dark-shadow lu)
\end{code}
%</norrish-type>

%<*norrish>
\begin{code}
⊨norrish ρ xs lu ⊭xs ⊨Ωlu =
  let ps = ⊨αβn<aβ≤αb<αβ[n+1] (⊨βa≤αb ⊨Ωlu ) ⊭xs
   in ⊭[α-1][β-1]≤αb-aβ (⊨α≤αβ[n+1]-αb ps) (⊨β≤aβ-αβn ps) ⊨Ωlu
  where open Norrish ρ lu 
\end{code}
%</norrish>

%<*by-contradiction-type>
\begin{code}
by-contradiction : ∀ {i} (ρ : Env i) (xs : List ℤ) (lus : List (Pair (suc i)))
                 → (⊨Ωlus : All ⊨[ ρ /x] (omega lus))
                 → (∀[ xs ] λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
                 → ⊥
\end{code}
%</by-contradiction-type>

%<*by-contradiction>
\begin{code}
by-contradiction {i} ρ xs lus ⊨Ωlus ∀xs¬∀lus =
  ¬∃lus→¬∃xs lus ⊨Ωlus (∀xs→¬∀lus⇒∃lus→¬∃xs ∀xs¬∀lus)
  where
\end{code}
%</by-contradiction>

%<*contradiction-search>
\begin{code}
  ¬∃lus→¬∃xs : (lus : List (Pair (suc i)))
             → (⊨Ωlus : All ⊨[ ρ /x] (omega lus))
             → (∃[ lus ] λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
             → ⊥

  ¬∃lus→¬∃xs [] [] ()
  ¬∃lus→¬∃xs (lu ∷ lus) (⊨Ωlu ∷ ⊨Ωlus) (here ¬∃xs)       = ⊨norrish ρ xs lu ¬∃xs ⊨Ωlu
  ¬∃lus→¬∃xs (lu ∷ lus) (⊨Ωlu ∷ ⊨Ωlus) (there ∃lus→¬∃xs) = ¬∃lus→¬∃xs lus ⊨Ωlus ∃lus→¬∃xs
\end{code}
%</contradiction-search>

%<*contradiction-adaptation>
\begin{code}
  postulate ∀lus∃xs⇒∃xs∀lus : (∀[ lus ] (λ lu → ∃[ xs ] (λ x → ⊨[ x ∷ ρ /x]ₚ lu)))
                            → (∃[ xs ] (λ x → ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ))

  ∀xs→¬∀lus⇒∃lus→¬∃xs : (∀[ xs ] λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
                      → (∃[ lus ] λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)

  ∀xs→¬∀lus⇒∃lus→¬∃xs = begin
    (∀[ xs ] λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
      ∼⟨ AllProp.All¬⇒¬Any ⟩
    (¬ ∃[ xs ] λ x → ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
      ∼⟨ (λ ¬∃xs∀lus ∀lus∃xs → ¬∃xs∀lus (∀lus∃xs⇒∃xs∀lus ∀lus∃xs)) ⟩
    (¬ ∀[ lus ] λ lu → ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
      ∼⟨ AllProp.¬All⇒Any¬ (λ lu → any (λ x → ⟦ lu ⟧[ x ∷ ρ /x]ₚ) xs) lus ⟩
    (∃[ lus ] λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
      ∎
    where open ⇒-Reasoning
\end{code}
%</contradiction-adaptation>

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

pairs : ∀ {i} (as : List (Linear (suc i))) → List (Pair (suc i)) 
pairs as = let lius = partition as in ×-list (proj₁ lius) (proj₂ (proj₂ lius))

irrels : ∀ {i} (as : List (Linear (suc i))) → List (Constraint (suc i) Irrelevant) 
irrels as = proj₁ (proj₂ (partition as))

_⊎?_ : {A : Set} {P Q : A → Set} {a : A} → Dec (P a) → Dec (Q a) → Dec (P a ⊎ Q a)
_⊎?_ (no ¬p) (no ¬q) = no λ { (inj₁ p) → ¬p p ; (inj₂ q) → ¬q q}
_⊎?_ (yes p) _       = yes (inj₁ p)
_⊎?_ _       (yes q) = yes (inj₂ q)

∀α≡1∨-β≡-1 : ∀ {i} (lus : List (Pair (suc i))) → Set
∀α≡1∨-β≡-1 lus = All (λ lu → head (proj₁ (proj₁ lu)) ≡ + 1 ⊎ head (proj₁ (proj₂ lu)) ≡ - + 1) lus

∀α≡1∨-β≡-1? : ∀ {i} → Decidable {A = List (Pair (suc i))} ∀α≡1∨-β≡-1
∀α≡1∨-β≡-1? lus = all (λ lu → (head (proj₁ (proj₁ lu)) ≟ + 1) ⊎? (head (proj₁ (proj₂ lu)) ≟ - + 1)) lus
\end{code}

%<*elimination>
\begin{code}
eliminate : ∀ {i} → List (Linear (suc i)) → List (Linear i)
eliminate as = elim-irrel (irrels as) ++ omega (pairs as)
       
interpret : ∀ {i} → List (Pair (suc i)) → Result → Result
interpret lus unsatisfiable with ∀α≡1∨-β≡-1? lus
...                         | yes _ = unsatisfiable
...                         | no _  = undecided
interpret lus r = r

⟦_⟧Ω : ∀ {i} → List (Linear i) → Result
⟦_⟧Ω {zero} as with all ⟦_⟧[ [] /x] as
...            | yes p = satisfiable
...            | no ¬p = unsatisfiable
⟦_⟧Ω {suc i} as = interpret (pairs as) ⟦ eliminate as ⟧Ω 
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
prepend-x ρ x (ir ∷ irs) (⊨Ωir ∷ ⊨Ωirs) rewrite ⊨cs≡⊨0∷cs ρ x ir = ⊨Ωir ∷ (prepend-x ρ x irs ⊨Ωirs)

strip-x : ∀ {i} (ρ : Env i) (x : ℤ) (irs : List (Constraint (suc i) Irrelevant))
        → All ⊨[ x ∷ ρ /x]ᵢ irs
        → All ⊨[ ρ /x] (elim-irrel irs)

strip-x ρ x [] [] = []
strip-x ρ x (ir ∷ irs) (⊨ir ∷ ⊨irs) rewrite sym (⊨cs≡⊨0∷cs ρ x ir) = ⊨ir ∷ (strip-x ρ x irs ⊨irs)
\end{code}
%</prepend-x>

%<*correct>
\begin{code}
tangle-×ˡ : {A B : Set} {P : A → Set} {Q : B → Set} (xs : List A) (ys : List B)
          → All P xs → All (λ {(x , y) → P x ⊎ Q y}) (×-list xs ys)
tangle-×ˡ xs [] Pxs = []
tangle-×ˡ {A} {B} {P} {Q} xs (y ∷ ys) Pxs = AllProp.++⁺ (inner y xs Pxs) (tangle-×ˡ xs ys Pxs)
  where
  inner : (y : B) (xs : List A) → All P xs → All (λ {(x , y) → P x ⊎ Q y}) (×-list-inner xs y)
  inner y [] [] = []
  inner y (x ∷ xs) (px ∷ Pxs) = (inj₁ px) ∷ (inner y xs Pxs)

tangle-×ʳ : {A B : Set} {P : A → Set} {Q : B → Set} (xs : List A) (ys : List B)
          → All Q ys → All (λ {(x , y) → P x ⊎ Q y}) (×-list xs ys)
tangle-×ʳ xs [] [] = []
tangle-×ʳ {A} {B} {P} {Q} xs (y ∷ ys) (Qy ∷ Qys) = AllProp.++⁺ (inner y xs Qy) (tangle-×ʳ xs ys Qys)
  where
  inner : (y : B) (xs : List A) → Q y → All (λ {(x , y) → P x ⊎ Q y}) (×-list-inner xs y)
  inner y [] Qy = []
  inner y (x ∷ xs) Qy = (inj₂ Qy) ∷ (inner y xs Qy)

foo : ∀ {i} (x : ℤ) (ρ : Env i) (lus : List (Pair (suc i)))
    → All (λ {((l , _) , (u , _)) → head l ≡ + 1 ⊎ head u ≡ - + 1}) lus
    → All ⊨[ x ∷ ρ /x]ₚ lus → All ⊨[ ρ /x] (omega lus)
foo x ρ [] [] [] = []
foo x ρ (lu@(((cl x+ csl +ℤ kl) , _) , ((cu x+ csu +ℤ ku) , _)) ∷ lus) (t ∷ ts) ((⊨l , ⊨u) ∷ ⊨lus) =
  Norrish.⊨real-shadow ρ lu x t ⊨l ⊨u ∷ (foo x ρ lus ts ⊨lus)

postulate tangle : ∀ {i} {P : Linear (suc i) → Set} (as : List (Linear (suc i)))
                 → All (λ lu → P (proj₁ (proj₁ lu)) × P (proj₁ (proj₂ lu))) (pairs as)
                 → All (λ i → P (proj₁ i)) (irrels as)
                 → All P as

postulate untangleʳ : ∀ {i} {P : Linear (suc i) → Set} (as : List (Linear (suc i)))
                   → All P as
                   → All (λ lu → P (proj₁ (proj₁ lu)) × P (proj₁ (proj₂ lu))) (pairs as)

postulate untangleˡ : ∀ {i} {P : Linear (suc i) → Set} (as : List (Linear (suc i)))
                   → All P as
                   → All (λ i → P (proj₁ i)) (irrels as)

unsat : ∀ {i} (as : List (Linear i)) → ⟦ as ⟧Ω ≡ unsatisfiable → ⊨ as → ⊥
unsat {zero} as ep with all ⟦_⟧[ [] /x] as
unsat {zero} as () | yes p
unsat {zero} as ep | no ¬p = λ {([] , ⊨as) → ¬p ⊨as}
unsat {suc i} as ep with ⟦ eliminate as ⟧Ω | inspect ⟦_⟧Ω (eliminate as)
unsat {suc i} as () | undecided | _
unsat {suc i} as () | satisfiable | _
unsat {suc i} as ep | unsatisfiable | j with ∀α≡1∨-β≡-1? (pairs as)
unsat {suc i} as () | unsatisfiable | j | no ¬∀α≡1∨-β≡-1
unsat {suc i} as ep | unsatisfiable | >[ eq ]< | yes ∀α≡1∨-β≡-1 with unsat (eliminate as) eq
... | z = λ { (x ∷ ρ , ⊨as) → z (ρ , AllProp.++⁺ (strip-x ρ x (irrels as) (untangleˡ as ⊨as)) (foo x ρ (pairs as) ∀α≡1∨-β≡-1 (untangleʳ as ⊨as)))}


sat : ∀ {i} (as : List (Linear i)) → ⟦ as ⟧Ω ≡ satisfiable → ⊨ as
sat {zero} as ep with all ⟦_⟧[ [] /x] as
sat {zero} as ep | yes p = [] , p
sat {zero} as () | no ¬p
sat {suc i} as ep with ⟦ eliminate as ⟧Ω | inspect ⟦_⟧Ω (eliminate as)
sat {suc i} as () | undecided | _
sat {suc i} as ep | unsatisfiable | _ with ∀α≡1∨-β≡-1? (pairs as)
sat {suc i} as () | unsatisfiable | _ | yes _
sat {suc i} as () | unsatisfiable | _ | no _ 
sat {suc i} as ep | satisfiable  | >[ eq ]< with sat (eliminate as) eq
sat {suc i} as ep | _ | _ | ρ , ⊨Ωas with AllProp.++⁻ (elim-irrel (irrels as)) ⊨Ωas
sat {suc i} as ep | _ | _ | ρ , ⊨Ωas | ⊨Ωirs , ⊨Ωlus with find-x ρ (pairs as) ⊨Ωlus
sat {suc i} as ep | _ | _ | ρ , ⊨Ωas | ⊨Ωirs , ⊨Ωlus | x , ⊨lus with prepend-x ρ x (irrels as) ⊨Ωirs
... | ⊨irs = (x ∷ ρ) , (tangle as ⊨lus ⊨irs)

⟦_⟧Ω-correct : ∀ {i} (as : List (Linear i)) → ⟦ as ⟧Ω-Correct
⟦_⟧Ω-correct as with ⟦ as ⟧Ω | inspect ⟦_⟧Ω as
⟦_⟧Ω-correct as | undecided     | _        = tt
⟦_⟧Ω-correct as | unsatisfiable | >[ eq ]< = unsat as eq
⟦_⟧Ω-correct as | satisfiable   | >[ eq ]< = sat as eq
\end{code}
%</correct>
