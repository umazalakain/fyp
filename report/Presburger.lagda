\begin{code}
module Presburger where

open import Function using (id ; _∘_)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Integer as Int hiding (suc)
open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Nat.Divisibility as Div
open import Data.Nat.DivMod using (_div_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec as Vec using (Vec ; [] ; _∷_)
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.List as List using (List ; [] ; _∷_ ; _++_)
open import Data.List.All using (All ; all ; [] ; _∷_)
open import Data.List.Any using (Any ; any ; here ; there)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

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
\end{code}

\section{Generic utilities}

\begin{code}
-- So that if predicates are nested, we can immediately see the subject
∀[_]_ : ∀ {a p} {A : Set a} → List A → (A → Set p) → Set (p ℓ⊔ a)
∀[ xs ] P = All P xs 

∃[_]_ : ∀ {a p} {A : Set a} → List A → (A → Set p) → Set (p ℓ⊔ a)
∃[ xs ] P = Any P xs 

×-list : {X Y : Set} → List X → List Y → List (X × Y)
×-list xs = List.concatMap λ y → List.map (_, y) xs

-- I don't have time for this
postulate x≤y+z≡x-z≤y : (x y z : ℤ) → (x ≤ y + z) ≡ (x - z ≤ y)
postulate 0≤n→m-n≤m : (m : ℤ) (n : ℤ) → (+ 0) ≤ n → m - n ≤ m
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

\section{Representation}

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

\section{Normal form}

%<*linear>
\begin{code}
record Linear (i : ℕ) : Set where
  constructor _∷+_
  field
    cs : Vec ℤ i
    k : ℤ
\end{code}
%</linear>

\section{Normal form utilities}

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

\section{Normalisation}

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
¬-dnf [] = []
¬-dnf (x ∷ []) = ¬-conjunction x
¬-dnf (x ∷ x' ∷ xs) = ¬-conjunction x ∧-dnf (¬-dnf (x' ∷ xs))
-- ¬-dnf_ = List.foldl (λ dnf conj → dnf ∧-dnf ¬-conjunction conj) (\n

_⇒-dnf_ : ∀ {i} → DNF i → DNF i → DNF i
xs ⇒-dnf ys = (¬-dnf xs) ∨-dnf (xs ∧-dnf ys)

∃-dnf_ : ∀ {i} → DNF (suc i) → DNF i
∃-dnf_ = List.map λ conj → 0≤ [] ∧ (∃ conj ∷ []) E
                                                   
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
%</normalisation>

\section{Elimination}

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

-- Must not pattern match so that we live a useful trail for unification
pairs : ∀ {i} (as : List (Linear (suc i))) → List (Pair (suc i)) 
pairs as = let lius = partition as in ×-list (proj₁ lius) (proj₂ (proj₂ lius))
irrels : ∀ {i} (as : List (Linear (suc i))) → List (Σ (Linear (suc i)) Irrelevant) 
irrels as = proj₁ (proj₂ (partition as))
\end{code}

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
elim-irrel : ∀ {i} → List (Σ (Linear (suc i)) Irrelevant) → List (Linear i)
elim-irrel = List.map (tail ∘ proj₁)

eliminate : ∀ {i} → List (Linear (suc i)) → List (Linear i)
eliminate as = elim-irrel (irrels as) ++ omega (pairs as)
\end{code}

\section{Verification}

%<*evaluation
\begin{code}
Env : ℕ → Set
Env i = Vec ℤ i

[_/x]_ : ∀ {i} → Env i → Linear i → ℤ
[_/x]_ [] ([] ∷+ k) = k
[_/x]_ (x ∷ xs) ((c ∷ cs) ∷+ k) = c * x + [ xs /x] (cs ∷+ k)
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

⊨[_/x]ᵢ : ∀ {i} → Env i → Σ (Linear i) Irrelevant → Set
⊨[ ρ /x]ᵢ (ir , _) = ⊨[ ρ /x] ir
\end{code}

%<*decidability>
\begin{code}
⊨?_[_/x] : ∀ {i} → (a : Linear i) → (ρ : Env i) → Dec (⊨[ ρ /x] a)
⊨? a [ ρ /x] = + 0 ≤? [ ρ /x] a

⊨?_[_/x]ₚ : ∀ {i} → (lu : Pair i) → (ρ : Env i) → Dec (⊨[ ρ /x]ₚ lu)
⊨? ((l , _) , (u , _)) [ ρ /x]ₚ with ⊨? l [ ρ /x] | ⊨? u [ ρ /x]
⊨? (l , _) , u , _ [ ρ /x]ₚ | yes pl | yes pu = yes (pl , pu)
⊨? (l , _) , u , _ [ ρ /x]ₚ | _      | no ¬pu = no λ {(_ , pu) → ¬pu pu}
⊨? (l , _) , u , _ [ ρ /x]ₚ | no ¬pl | _      = no λ {(pl , _) → ¬pl pl}
\end{code}
%</decidability>

%<*meaning-all>
\begin{code}
⊨ : ∀ {i} → List (Linear i) → Set
⊨ {i} as = Σ (Env i) λ ρ → ∀[ as ] ⊨[ ρ /x]
\end{code}
%</meaning-all>

\subsection{Verification lemmas}

\begin{code}
[_/x]-⊕ : ∀ {i} (ρ : Env i) (a b : Linear i) → [ ρ /x] (a ⊕ b) ≡ [ ρ /x] a + [ ρ /x] b
[ [] /x]-⊕ ([] ∷+ ka) ([] ∷+ kb) = refl
[ x ∷ ρ /x]-⊕ ((ca ∷ csa) ∷+ ka) ((cb ∷ csb) ∷+ kb)
  rewrite [ ρ /x]-⊕ (csa ∷+ ka) (csb ∷+ kb) = begin 
  (ca + cb) * x + ([ ρ /x] (csa ∷+ ka) + [ ρ /x] (csb ∷+ kb))
    ≡⟨ cong (λ ● → ● + _) (IntProp.distribʳ x ca cb) ⟩
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
    ≡⟨ sym (IntProp.distribʳ n (c * x) _) ⟩
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
  | IntProp.doubleNeg ([ ρ /x] a)
  | IntProp.doubleNeg ([ ρ /x] b)
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

-- div requires an implicit proof showing its divisor is non-zero
a/α : ∀ {i} → Env i → Σ (Linear (suc i)) LowerBound → ℤ
a/α ρ (+_ zero x+ -cs +ℤ -k , (_≤_.+≤+ ()))
a/α ρ (+_ (suc α-1) x+ -cs +ℤ -k , lb) = let a = - [ ρ /x] (-cs ∷+ -k) in sign a ◃ (∣ a ∣ div suc α-1)
a/α ρ (-[1+ n ] x+ -cs +ℤ -k , ())

b/β : ∀ {i} → Env i → Σ (Linear (suc i)) UpperBound → ℤ
b/β ρ (+_ c x+ cs +ℤ k , _≤_.+≤+ ())
b/β ρ (-[1+ β-1 ] x+ cs +ℤ k , ub) = let b = [ ρ /x] (cs ∷+ k) in sign b ◃ (∣ b ∣ div suc β-1)
\end{code}
   
\subsection{Norrish}

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
      ≡⟨ cong (λ ● → (α * x + [ ρ /x] ●) * (+ suc n)) (sym (⊝⊝a≡a -a)) ⟩
    (α * x + [ ρ /x] (⊝ a)) * (+ suc n)
      ≡⟨ cong (λ ● → (α * x + ●) * (+ suc n)) ([ ρ /x]-⊝ a) ⟩
    (α * x + - [ ρ /x] a) * (+ suc n)
      ≡⟨ IntProp.distribʳ (+ suc n) (α * x) (- [ ρ /x] a) ⟩
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
         → ¬ ⊨[ ρ /x] (dark-shadow lu)
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

\subsection{Search}

%<*search-space>
\begin{code}
start : ∀ {i} → Env i → List (Σ (Linear (suc i)) LowerBound) → ℤ
start ρ ls = List.foldr _⊔_ (+ 0) (List.map (a/α ρ) ls)

stop : ∀ {i} → Env i → List (Σ (Linear (suc i)) UpperBound) → ℤ
stop ρ us = List.foldr _⊓_ (+ 0) (List.map (b/β ρ) us)

search-space : ∀ {i} → Env i → List (Pair (suc i)) → List ℤ
search-space ρ lus with start ρ (List.map proj₁ lus)
search-space ρ lus | Δ₀ with stop ρ (List.map proj₂ lus) - Δ₀
search-space ρ lus | Δ₀ | + n = List.applyUpTo (λ i → + i + Δ₀) n 
search-space ρ lus | Δ₀ | -[1+ n ] = []
\end{code}
%</search-space>

%<*by-contradiction-type>
\begin{code}
by-contradiction : ∀ {i} (ρ : Env i) (xs : List ℤ) (lus : List (Pair (suc i)))
                 → ∀[ omega lus ] ⊨[ ρ /x]
                 → ∀[ xs ] (λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
                 → ⊥
\end{code}
%</by-contradiction-type>

%<*by-contradiction>
\begin{code}
by-contradiction {i} ρ xs lus ⊨lus↓ ∀xs¬∀lus =
  ¬∃lus→¬∃xs lus ⊨lus↓ (∀xs→¬∀lus⇒∃lus→¬∃xs ∀xs¬∀lus)
  where
\end{code}
%</by-contradiction>

%<*contradiction-search>
\begin{code}
  ¬∃lus→¬∃xs : (lus : List (Pair (suc i)))
             → ∀[ omega lus ] ⊨[ ρ /x]
             → ∃[ lus ] (λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)
             → ⊥

  ¬∃lus→¬∃xs [] [] ()
  ¬∃lus→¬∃xs (lu ∷ lus) (⊨lu↓ ∷ ⊨lus↓) (here ¬∃xs)       = ⊨norrish ρ xs lu ¬∃xs ⊨lu↓
  ¬∃lus→¬∃xs (lu ∷ lus) (⊨lu↓ ∷ ⊨lus↓) (there ∃lus→¬∃xs) = ¬∃lus→¬∃xs lus ⊨lus↓ ∃lus→¬∃xs
\end{code}
%</contradiction-search>

%<*contradiction-adaptation>
\begin{code}
  postulate ∀lus∃xs⇒∃xs∀lus : ∀[ lus ] (λ lu → ∃[ xs ] (λ x → ⊨[ x ∷ ρ /x]ₚ lu))
                            → ∃[ xs ] (λ x → ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)

  ∀xs→¬∀lus⇒∃lus→¬∃xs : ∀[ xs ] (λ x → ¬ ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ)
                      → ∃[ lus ] (λ lu → ¬ ∃[ xs ] λ x → ⊨[ x ∷ ρ /x]ₚ lu)

  ∀xs→¬∀lus⇒∃lus→¬∃xs = begin
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

%<*find-x>
\begin{code}
find-x : ∀ {i} (ρ : Env i) (lus : List (Pair (suc i)))
       → ∀[ omega lus ] ⊨[ ρ /x]
       → Σ ℤ λ x → ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ

find-x ρ lus ⊨lus↓ with search-space ρ lus
find-x ρ lus ⊨lus↓ | xs = search (λ x → all ⊨?_[ x ∷ ρ /x]ₚ lus ) xs (by-contradiction ρ xs lus ⊨lus↓)
\end{code}
%</find-x>

\subsection{Soundness}

%<*result>
\begin{code}
data Result : Set where
  satisfiable unsatisfiable undecided : Result
\end{code}
%</result>

\begin{code}
α≡1∨-β≡-1 : ∀ {i} (lu : Pair (suc i)) → Set
α≡1∨-β≡-1 lu = head (proj₁ (proj₁ lu)) ≡ + 1 ⊎ head (proj₁ (proj₂ lu)) ≡ - + 1

α≡1∨-β≡-1? : ∀ {i} → Decidable {A = Pair (suc i)} α≡1∨-β≡-1
α≡1∨-β≡-1? ((l , _) , (u , _)) with head l ≟ + 1 | head u ≟ - + 1
... | no ¬α≡1 | no ¬-β≡-1 = no λ { (inj₁ α≡1) → ¬α≡1 α≡1 ; (inj₂ -β≡-1) → ¬-β≡-1 -β≡-1}
... | yes α≡1 | _         = yes (inj₁ α≡1)
... | _       | yes -β≡-1 = yes (inj₂ -β≡-1)
\end{code}

%<*elimination>
\begin{code}
Ω : ∀ {i} → List (Linear i) → Result
Ω {zero}  as with all ⊨?_[ [] /x] as
Ω {zero}  as | yes _ = satisfiable
Ω {zero}  as | no _  = unsatisfiable
Ω {suc i} as with Ω (eliminate as)
Ω {suc i} as | unsatisfiable with all α≡1∨-β≡-1? (pairs as)
Ω {suc i} as | unsatisfiable | yes _ = unsatisfiable
Ω {suc i} as | unsatisfiable | no _  = undecided
Ω {suc i} as | r                     = r
\end{code}
%</elimination>

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
⊨Ωlus : ∀ {i} (x : ℤ) (ρ : Env i) (lus : List (Pair (suc i)))
      → ∀[ lus ] α≡1∨-β≡-1 
      → ∀[ lus ] ⊨[ x ∷ ρ /x]ₚ
      → ∀[ omega lus ] ⊨[ ρ /x]
⊨Ωlus x ρ [] [] [] = []
⊨Ωlus x ρ (lu@(((_ x+ _ +ℤ _) , _) , ((_ x+ _ +ℤ _) , _)) ∷ lus) (t ∷ ts) ((⊨l , ⊨u) ∷ ⊨lus) =
  Norrish.⊨real-shadow ρ lu x t ⊨l ⊨u ∷ (⊨Ωlus x ρ lus ts ⊨lus)

prepend-x : ∀ {i} (x : ℤ) (ρ : Env i) (irs : List (Σ (Linear (suc i)) Irrelevant))
          → ∀[ elim-irrel irs ] ⊨[ ρ /x]
          → ∀[ irs ] ⊨[ x ∷ ρ /x]ᵢ

prepend-x x ρ [] [] = []
prepend-x x ρ (ir ∷ irs) (⊨ir↓ ∷ ⊨irs↓) rewrite ⊨cs≡⊨0∷cs x ρ ir = ⊨ir↓ ∷ (prepend-x x ρ irs ⊨irs↓)

strip-x : ∀ {i} (x : ℤ) (ρ : Env i) (irs : List (Σ (Linear (suc i)) Irrelevant))
        → ∀[ irs ] ⊨[ x ∷ ρ /x]ᵢ
        → ∀[ elim-irrel irs ] ⊨[ ρ /x]

strip-x x ρ [] [] = []
strip-x x ρ (ir ∷ irs) (⊨ir ∷ ⊨irs) rewrite sym (⊨cs≡⊨0∷cs x ρ ir) = ⊨ir ∷ (strip-x x ρ irs ⊨irs)
\end{code}

\begin{code}
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
unsat : ∀ {i} (as : List (Linear i)) → Ω as ≡ unsatisfiable → ⊨ as → ⊥
unsat {zero} as ep with all ⊨?_[ [] /x] as
unsat {zero} as () | yes p
unsat {zero} as ep | no ¬p = λ {([] , ⊨as) → ¬p ⊨as}
unsat {suc i} as ep with Ω (eliminate as) | inspect Ω (eliminate as)
unsat {suc i} as () | undecided     | _
unsat {suc i} as () | satisfiable   | _
unsat {suc i} as ep | unsatisfiable | _        with all α≡1∨-β≡-1? (pairs as)
unsat {suc i} as () | unsatisfiable | _        | no ¬∀α≡1∨-β≡-1
unsat {suc i} as ep | unsatisfiable | >[ eq ]< | yes ∀α≡1∨-β≡-1 with unsat (eliminate as) eq
unsat {suc i} as ep | unsatisfiable | >[ eq ]< | yes ∀α≡1∨-β≡-1 | ⊨as↓→⊥ = λ {
  (x ∷ ρ , ⊨as) → ⊨as↓→⊥ (ρ , AllProp.++⁺
    (strip-x x ρ (irrels as) (untangleᵢ as ⊨as))
    (⊨Ωlus x ρ (pairs as) ∀α≡1∨-β≡-1 (untangleₚ as ⊨as)))}

sat : ∀ {i} (as : List (Linear i)) → Ω as ≡ satisfiable → ⊨ as
sat {zero} as ep with all ⊨?_[ [] /x] as
sat {zero} as ep | yes p = [] , p
sat {zero} as () | no ¬p
sat {suc i} as ep with Ω (eliminate as) | inspect Ω (eliminate as)
sat {suc i} as () | undecided | _
sat {suc i} as ep | unsatisfiable | _ with all α≡1∨-β≡-1? (pairs as)
sat {suc i} as () | unsatisfiable | _ | yes _
sat {suc i} as () | unsatisfiable | _ | no _ 
sat {suc i} as ep | satisfiable  | >[ eq ]< with sat (eliminate as) eq
sat {suc i} as ep | _ | _ | ρ , ⊨as↓ with AllProp.++⁻ (elim-irrel (irrels as)) ⊨as↓
sat {suc i} as ep | _ | _ | ρ , ⊨as↓ | ⊨irs↓ , ⊨lus↓ with find-x ρ (pairs as) ⊨lus↓
sat {suc i} as ep | _ | _ | ρ , ⊨as↓ | ⊨irs↓ , ⊨lus↓ | x , ⊨lus with prepend-x x ρ (irrels as) ⊨irs↓
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
