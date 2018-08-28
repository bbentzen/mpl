/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic

variable σ : nat

/- code & encode -/

def atom_code (α : var σ) : form σ → Prop
 | (#p) := (α = p)
 |   ⊥    := false
 | (p ⊃ q) := false

def atom_encode (α : var σ) (x : form σ) :
  #α = x → atom_code σ α x :=
by intro h; induction h; unfold atom_code

def neg_code (α : form σ) : form σ → Prop
 | (#p) := false
 |   ⊥    := (α = ⊥)
 | (p ⊃ q) := false

def neg_encode (x : form σ) :
   ⊥ = x → neg_code σ ⊥ x :=
by intro h; induction h; unfold neg_code

def impl_code (α β : form σ) : form σ → Prop
 | (#p) := false
 |   ⊥    := false
 | (p ⊃ q) := (α = p) ∧ (β = q)

def impl_encode (α β x : form σ) :
  (α ⊃ β) = x → impl_code σ α β x :=
by intro h; induction h; unfold impl_code;  apply and.intro; simp

/- propositional equalities -/

def atom_eq (p q : var σ) :
  #p = #q → p = q :=
by apply atom_encode

def impl_eq (p q p' q' : form σ) :
  (p ⊃ q) = (p' ⊃ q') → (p = p') ∧ (q = q') :=
by apply impl_encode

def neg_eq (p q : form σ) :
   (~p) = (~q) → p = q :=
by intro h; apply and.elim_left; apply impl_eq; exact h

/- propositional inequalities -/

def atom_neq_bot (p : var σ) (p₁ q₂ : form σ) :
  #p ≠ ⊥ :=
have hn : atom_code σ p ⊥ → false := id,
  λ h, hn (atom_encode _ p ⊥ h)

def atom_neq_impl (p : var σ) (p₁ q₂ : form σ) :
  (#p) ≠ (p₁ ⊃ q₂) :=
have hn : atom_code σ p (p₁ ⊃ q₂) → false := id,
  λ h, hn (atom_encode _ p (p₁ ⊃ q₂) h)

def bot_neq_impl (p q : form σ) :
  ⊥ ≠ (p ⊃ q) :=
have hn : neg_code σ ⊥ (p ⊃ q) → false := id,
  λ h, hn (neg_encode _ (p ⊃ q) h)
