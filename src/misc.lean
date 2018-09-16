/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

-- some general lemmas used in this project

def contrap {p q : Prop} : 
  (p → q) ↔ (¬ q → ¬ p) :=
iff.intro (λ f nq p, nq (f p))
 (λ f hp, or.elim (classical.em q) id (λ nq, false.elim ((f nq) hp)))

def not_contrap {p q : Prop} : 
  (¬ q → ¬ p) → (p → q) :=
contrap.2

