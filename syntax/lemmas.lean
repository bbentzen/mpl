/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic

open list nat bool

/- deduction metatheorem -/

def deduction {Γ : ctx} {p q : form} :
  (Γ ⸴ p ⊢ₖ q) ⇒ (Γ ⊢ₖ p ⊃ q) :=
begin
 intro H,
 induction H,
   exact prf.mp prf.pl1 prf.pl1,
   exact prf.mp prf.pl1 (prf.pl2),
   exact prf.mp prf.pl1 (prf.pl3),
   exact prf.mp (prf.mp prf.pl2 H_ih_d₁) H_ih_d₂,
   exact prf.mp prf.pl1 prf.k,
   exact prf.mp prf.pl1 (prf.nec H_d)
end

/- structural rules -/

def weak (p q : form) (Γ : ctx):
  (Γ ⊢ₖ p) ⇒ (Γ ⸴ q ⊢ₖ p) :=
begin
  intro H,
  induction H,
    exact prf.pl1,
    exact prf.pl2,
    exact prf.pl3,
    exact prf.mp H_ih_d₁ H_ih_d₂,
    exact prf.k,
    exact prf.nec H_d
end

def contr (p q : form) (Γ : ctx):
  (Γ ⸴ p ⸴ p ⊢ₖ q) ⇒ (Γ ⸴ p ⊢ₖ q) :=
begin
  intro H,
  induction H,
    exact prf.pl1,
    exact prf.pl2,
    exact prf.pl3,
    exact prf.mp H_ih_d₁ H_ih_d₂,
    exact prf.k,
    exact prf.nec H_d
end

def exg (p q r : form) (Γ : ctx):
  (Γ ⸴ p ⸴ q ⊢ₖ r) ⇒ (Γ ⸴ q ⸴ p ⊢ₖ r) :=
begin
  intro H,
  induction H,
    exact prf.pl1,
    exact prf.pl2,
    exact prf.pl3,
    exact prf.mp H_ih_d₁ H_ih_d₂,
    exact prf.k,
    exact prf.nec H_d
end

/- basic rules of inference -/

def pr {p : form} {Γ : ctx} :
  Γ ⸴ p ⊢ₖ p :=
by apply ax; apply or.intro_left; simp

def pr1 {p q : form} {Γ : ctx} :
  Γ ⸴ p ⸴ q ⊢ₖ p :=
by apply ax; apply or.intro_right; apply or.intro_left; simp

def pr2 {p q : form} {Γ : ctx} :
  Γ ⸴ p ⸴ q ⊢ₖ q :=
by apply ax; apply or.intro_left; simp

def cut {p q r : form} {Γ : ctx} :
  (Γ ⊢ₖ p ⊃ q) ⇒ (Γ ⊢ₖ q ⊃ r) ⇒ (Γ ⊢ₖ p ⊃ r) :=
λ H1 H2, prf.mp (prf.mp prf.pl2 (prf.mp prf.pl1 H2 )) H1

/- basic lemmas -/

def implid {p : form} {Γ : ctx} :
  Γ ⊢ₖ p ⊃ p :=
deduction pr

def contrap {p q : form} {Γ : ctx} :
  Γ ⊢ₖ ((~q) ⊃ (~p)) ⊃ (p ⊃ q) :=
deduction (deduction
  (prf.mp (prf.mp prf.pl3 
    begin
      apply weak,
        apply ax,
          apply or.intro_left,
          simp 
    end
  ) 
  begin
    apply prf.mp,
      exact prf.pl1,
      apply ax,
        apply or.intro_left,
        simp
   end 
  )
)

