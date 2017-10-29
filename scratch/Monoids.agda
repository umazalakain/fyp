{-# OPTIONS --type-in-type #-}  -- yes, I will let you cheat in this exercise

module Monoids where

open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat

data _≡_ {X : Set} : X -> X -> Set where
  refl : (x : X) -> x ≡ x           -- the relation that's "only reflexive"
{-# BUILTIN EQUALITY _≡_ #-}
  
_[QED] : {X : Set}(x : X) -> x ≡ x
x [QED] = refl x

_=[_>=_ : {X : Set}(x : X){y z : X} -> x ≡ y -> y ≡ z -> x ≡ z
x =[ refl .x >= q = q

_=<_]=_ : {X : Set}(x : X){y z : X} -> y ≡ x -> y ≡ z -> x ≡ z
x =< refl .x ]= q = q

infixr 1 _=[_>=_ _=<_]=_
infixr 2 _[QED]

_=$=_ : {X Y : Set}{f f' : X -> Y}{x x' : X} ->
        f ≡ f' -> x ≡ x' -> f x ≡ f' x'
refl f =$= refl x = refl (f x)
infixl 2 _=$=_

_++_ : ∀ {X} → List X → List X → List X
[] ++ q = q
(x ∷ p) ++ q = x ∷ p ++ q

data Expr (X : Set) : Set where
  var : X              → Expr X
  neut :                 Expr X
  op : Expr X → Expr X → Expr X

data Maybe (X : Set) : Set where
  yes : X → Maybe X
  no :      Maybe X
  
record Comp (X : Set) : Set where
  field
    comp : (x y : X) → Maybe (x ≡ y)

open Comp

record Env (X M : Set) : Set where
  field
    e : M
    o : M → M → M
    v : X → M
    law-e-o : (m : M) → o e m ≡ m
    law-o-e : (m : M) → m ≡ o m e
    law-o-o : (x y z : M) → o (o x y) z ≡ o x (o y z)

open Env

exprList : ∀ {X} → Expr X → List X
exprList (var x) = x ∷ []
exprList neut = []
exprList (op i j) = exprList i ++ exprList j

evalList : ∀ {X M} → Env X M → List X → M
evalList env [] = (e env)
evalList env (x ∷ xs) = (o env) ((v env) x) (evalList env xs)

evalExpr : ∀ {X M} → Env X M → Expr X → M
evalExpr env (var x) = (v env) x
evalExpr env neut = e env
evalExpr env (op xs ys) = (o env) (evalExpr env xs) (evalExpr env ys)

eval-distr : ∀ {X M} → (env : Env X M) → (p q : List X) →
             (o env) (evalList env p) (evalList env q) ≡ evalList env (p ++ q)
eval-distr env [] q = (law-e-o env) _
eval-distr env (x ∷ p) q = 
  (o env) ((o env) ((v env) x) (evalList env p)) (evalList env q)
    =[ (law-o-o env) _ _ _ >=
  (o env) ((v env) x) ((o env) (evalList env p) (evalList env q))
    =[ refl ((o env) ((v env) x)) =$= eval-distr env p q >=
  (o env) ((v env) x) (evalList env (p ++ q)) [QED]

eval-homomorphism : ∀ {X M} → (env : Env X M) → (expr : Expr X) →
                    evalExpr env expr ≡ evalList env (exprList expr)     
eval-homomorphism env (var x) = (law-o-e env) _
eval-homomorphism env neut = refl (e env)
eval-homomorphism env (op p q) rewrite
    eval-homomorphism env p
  | eval-homomorphism env q = eval-distr env (exprList p) (exprList q)

compareList : ∀ {X} → (p : List X) → (q : List X) → ((x : X) → (y : X) → Maybe (x ≡ y)) → Maybe (p ≡ q)
compareList [] [] f = yes (refl [])
compareList [] (x ∷ q) f = no
compareList (x ∷ p) [] f = no
compareList (x ∷ p) (y ∷ q) f with f x y | compareList p q f
compareList (x ∷ p) (y ∷ q) f | no | _ = no
compareList (x ∷ p) (y ∷ q) f | yes _ | no = no
compareList (x ∷ p) (y ∷ q) f | yes h | yes t = yes (refl _∷_ =$= h =$= t)

Fact : ∀ {X} → Expr X → Expr X → Comp X → Set
Fact {X} p q c with compareList (exprList p) (exprList q) (comp c)
... | yes _ = ∀ {M} → (env : Env X M) → evalExpr env p ≡ evalExpr env q
... | no = ⊤

fact : ∀ {X} → (p : Expr X) → (q : Expr X) → (f : Comp X) → Fact p q f
fact p q c with compareList (exprList p) (exprList q) (comp c)
fact p q c | yes leq = λ env → 
  evalExpr env p
    =[ eval-homomorphism env p >=
  evalList env (exprList p)
    =[ refl (evalList env) =$= leq >=
  evalList env (exprList q)
    =< eval-homomorphism env q ]=
  evalExpr env q [QED]
fact p q c | no = tt 

{-
  EXAMPLE: Natural numbers with addition, expressions indexed by natural numbers
-}
  
nat-env : Env Nat Nat
nat-env = record
               { e = 0
               ; o = _+_
               ; v = λ x → x
               ; law-e-o = refl
               ; law-o-e = right-0
               ; law-o-o = assoc
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
nat-expr-1 = op
  (op 
    (op neut neut)
    (op (op (var 1) neut) (var 2)))
  (op
    (op (var 1) (var 3))
    (var 2))

nat-expr-2 : Expr Nat
nat-expr-2 = op
  (var 1)
  (op
    (var 2)
    (op
      (var 1)
        (op (var 3) (var 2))))

nat-fact : (env : Env Nat Nat) → evalExpr env nat-expr-1 ≡ evalExpr env nat-expr-2
nat-fact = fact nat-expr-1 nat-expr-2 comp-nat

nat-answer : evalExpr nat-env nat-expr-1 ≡ evalExpr nat-env nat-expr-2
nat-answer = 9 [QED]
