module Monoids where

open import Agda.Builtin.List
open import Agda.Builtin.Nat

data _≡_ {X : Set} : X → X → Set where
  refl : (x : X) → x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
  
_[QED] : {X : Set}(x : X) → x ≡ x
x [QED] = refl x

_=[_>=_ : {X : Set}(x : X){y z : X} → x ≡ y → y ≡ z → x ≡ z
x =[ refl .x >= q = q

_=<_]=_ : {X : Set}(x : X){y z : X} → y ≡ x → y ≡ z → x ≡ z
x =< refl .x ]= q = q

infixr 1 _=[_>=_ _=<_]=_
infixr 2 _[QED]

_=$=_ : {X Y : Set}{f f' : X → Y}{x x' : X} →
        f ≡ f' → x ≡ x' → f x ≡ f' x'
refl f =$= refl x = refl (f x)
infixl 2 _=$=_

_++_ : {X : Set} → List X → List X → List X
[] ++ q = q
(x ∷ p) ++ q = x ∷ p ++ q

record ⊤₁ : Set₁ where
  constructor ⊤

data Expr (X : Set) : Set where
  var'  : X               → Expr X
  neut' :                   Expr X
  op'   : Expr X → Expr X → Expr X

data Maybe (X : Set) : Set where
  yes : X → Maybe X
  no  :     Maybe X
  
record Comp (X : Set) : Set where
  field
    comp : (x y : X) → Maybe (x ≡ y)

open Comp

record Env (X M : Set) : Set where
  field
    neut : M
    op : M → M → M
    var : X → M
    law-neut-op : (m : M) → op neut m ≡ m
    law-op-neut : (m : M) → m ≡ op m neut
    law-op-op : (x y z : M) → op (op x y) z ≡ op x (op y z)

  
exprList : ∀ {X} → Expr X → List X
exprList (var' x) = x ∷ []
exprList neut' = []
exprList (op' i j) = exprList i ++ exprList j

module _ {X M : Set} (env : Env X M) where
  open Env env

  evalList : List X → M
  evalList [] = neut
  evalList (x ∷ xs) = op (var x) (evalList xs)

  evalExpr : Expr X → M
  evalExpr (var' x) = var x
  evalExpr neut' = neut
  evalExpr (op' xs ys) = op (evalExpr xs) (evalExpr ys)

  eval-distr : (p q : List X) → (op (evalList p) (evalList q)) ≡ evalList (p ++ q )
  eval-distr [] q = law-neut-op _
  eval-distr (x ∷ p) q = 
    op (op (var x) (evalList p)) (evalList q)
      =[ law-op-op _ _ _ >=    op (var x) (op (evalList p) (evalList q))
      =[ refl (op  (var x)) =$= eval-distr p q >=
    op (var x) (evalList (p ++ q)) [QED]

  eval-commutes : (expr : Expr X) → evalExpr expr ≡ evalList (exprList expr)     
  eval-commutes (var' x) = law-op-neut _
  eval-commutes neut' = refl neut
  eval-commutes (op' p q) rewrite
                eval-commutes p
                | eval-commutes q = eval-distr (exprList p) (exprList q)

compareList : ∀ {X} → (p : List X) → (q : List X) → ((x : X) → (y : X) → Maybe (x ≡ y)) → Maybe (p ≡ q)
compareList [] [] f = yes (refl [])
compareList [] (x ∷ q) f = no
compareList (x ∷ p) [] f = no
compareList (x ∷ p) (y ∷ q) f with f x y | compareList p q f
compareList (x ∷ p) (y ∷ q) f | no | _ = no
compareList (x ∷ p) (y ∷ q) f | yes _ | no = no
compareList (x ∷ p) (y ∷ q) f | yes h | yes t = yes (refl _∷_ =$= h =$= t)

Fact : ∀ {X} → Expr X → Expr X → Comp X → Set₁
Fact {X} p q c with compareList (exprList p) (exprList q) (comp c)
... | yes _ = ∀ {M : Set} → (env : Env X M) → evalExpr env p ≡ evalExpr env q
... | no = ⊤₁

fact : ∀ {X} → (p : Expr X) → (q : Expr X) → (f : Comp X) → Fact p q f
fact p q c with compareList (exprList p) (exprList q) (comp c)
fact p q c | yes leq = λ env → 
  evalExpr env p
    =[ eval-commutes env p >=
  evalList env (exprList p)
    =[ refl (evalList env) =$= leq >=
  evalList env (exprList q)
    =< eval-commutes env q ]=
  evalExpr env q [QED]
fact p q c | no = ⊤

{-
  EXAMPLE: Natural numbers with addition, expressions indexed by natural numbers
-}
  
nat-env : Env Nat Nat
nat-env = record
               { neut = 0
               ; op = _+_
               ; var = λ x → x
               ; law-neut-op = refl
               ; law-op-neut = right-0
               ; law-op-op = assoc
               }
               where
               right-0 : ∀ m → m ≡ (m + 0)
               right-0 zero = refl zero
               right-0 (suc m) = refl suc =$= right-0 m
               
               assoc : ∀ x y z → ((x + y) + z) ≡ (x + (y + z))
               assoc zero y z = refl (y + z)
               assoc (suc x) y z rewrite assoc x y z = refl _
               
nat-comp : (x y : Nat) → Maybe (x ≡ y)
nat-comp zero zero = yes (refl zero)
nat-comp zero (suc y) = no
nat-comp (suc x) zero = no
nat-comp (suc x) (suc y) with nat-comp x y
nat-comp (suc x) (suc y) | yes z = yes (refl suc =$= z)
nat-comp (suc x) (suc y) | no = no

comp-nat : Comp Nat
comp-nat = record { comp = nat-comp }

nat-expr-1 : Expr Nat
nat-expr-1 = op'
  (op' 
    (op' neut' neut')
    (op' (op' (var' 1) neut') (var' 2)))
  (op'
    (op' (var' 1) (var' 3))
    (var' 2))

nat-expr-2 : Expr Nat
nat-expr-2 = op'
  (var' 1)
  (op'
    (var' 2)
    (op'
      (var' 1)
        (op' (var' 3) (var' 2))))

nat-expr-3 : Expr Nat
nat-expr-3 = neut'

nat-fact : (env : Env Nat Nat) → evalExpr env nat-expr-1 ≡ evalExpr env nat-expr-2
nat-fact = fact nat-expr-1 nat-expr-2 comp-nat

nat-answer : evalExpr nat-env nat-expr-1 ≡ evalExpr nat-env nat-expr-2
nat-answer = nat-fact nat-env

nat-answer₁ : nat-fact nat-env ≡ refl 9
nat-answer₁ = (refl 9) [QED]

nat-lie : ⊤₁
nat-lie = fact nat-expr-1 nat-expr-3 comp-nat
