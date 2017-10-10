---
title: Evidence providing problem solvers in Agda
subtitle: Project outline
author: Unai Zalakain
date: October 2017
---

# Overview

Agda is a dependently typed functional language in which the typechecker
executes parts of the program relevant to determining the correctness of the
types within that program. 

If we can encode an existing problem solving algorithm in such a way
that it hands back enough type information to assert the validity of its answer,
then the typechecker alone will be able to confirm its correctness at compile
time.

These types can either represent proofs by construction, where we show
step-by-step how to get to the answer following only valid inference rules
encoded into types, or proofs that show that the answer makes some predicates
hold.

The aim of this project is to translate into Agda some existing problem solver
algorithms so that the validity of their answers is proven by the type of their
answers, and can therefore be checked by Agda's typechecker.

<!--
Most problem solving algorithms take a problem description and answer either
with the data that solve the problem or the claim that the problem is impossible
to solve. In the dependently typed functional programming language Agda, data
can represent evidence, so a problem solving algorithm could potentially return
not only the solution, but the evidence that the returned data really does solve
the problem.

The purpose of this project is to select existing solvers for some problem
domains and make them deliver evidence that can be confirmed by typechecking
alone. In doing so, we increase the level of automation in Agda without having
to trust external solvers.
-->

# Blog

<https://devweb2017.cis.strath.ac.uk/~seb14166/>

# Objectives

- To better understand how Agda's type checker works.
- To understand how to model problem solvers in a dependently typed language.
- To learn from Agda's stdlib.
- To successfully implement some of these solvers for:
    - Commutative monoids
    - Monoids
    - Presburger arithmetic
    - SAT
    - Unification
    - Substitution
    - Other proofs that everyday Agda users would want to have available.

# Related work

- _Agda's stdlib_ by the community of Agda developers
- _Ring solving_ by Samnuel Boutin
- _Bounded quantification_ by Martijen Oostdijk
- _Theorems for Free_ by Philip Wadler
- _Dependently Typed Programming in Agda_ by Ulf Norell and James Chapman
- _A Brief Overview of Agda – A Functional Language with Dependent Types_ by Ana Bove, Peter Dybjer, and Ulf Norell
- _Engineering Proof by Reflection in Agda_ by Paul van der Walt and Wouter Swierstra

# Methodology

1. Better understand the problem domain (reading, talking to people).
2. Solve a problem with a good interest/difficulty ratio.
3. Reflect on the strategies used.
4. Go to 2.
5. Compare and evaluate different problem domains and solutions.

# Evaluation

- Compare solvers for different types of problems.
- Try out solvers in real world situations.

# Schedule

- First semester:
    - Gather requirements by the people routinely using Agda.
    - Reading
    - Do an easy problem
- Second semester:
    - Do more problems.
    - Compare and evaluate.
    - Complete writing.

# Marking scheme

Experimentation-based with Significant Software Development Project.

- Understanding problems and foreseeing implementations requires research.
- Implementations involve engineering.
