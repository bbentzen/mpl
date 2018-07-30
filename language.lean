/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

namespace mpl
open list nat bool

/- language -/

definition var : Type := nat

inductive form : Type
| atom : var → form
| neg : form → form
| impl : form → form → form 
| box : form → form

notation `~` p := form.neg p
notation p `⊃` q := form.impl p q
notation `◻` p := form.box p
notation `◇` p := ~ ◻ ~ p
notation p `&` q := ~ (p ⊃ ~q)
notation p `∨` q := ~ (~p & ~q)

/- the K system -/

def ctx : Type := list form

notation Γ `⸴` p := cons p Γ
notation Γ `∪` Ψ := append Γ Ψ
notation `{` p `}` := [p]  

inductive prf : ctx → form → Type 
| pl1 {Γ : ctx} {p q : form} : prf Γ (p ⊃ (q ⊃ p))
| pl2 {Γ : ctx} {p q r : form} : prf Γ ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))
| pl3 {Γ : ctx} {p q : form} :  prf Γ (((~q) ⊃ ~p) ⊃ ((q ⊃ p) ⊃ p))
| mp {Γ : ctx}  {p q : form} (d₁: prf Γ (p ⊃ q)) (d₂ : prf Γ p) : prf Γ q
| k {Γ : ctx}  {p q : form} : prf Γ ((◻(p ⊃ q)) ⊃ (◻p ⊃ ◻q))
| nec {Γ : ctx} {p : form} (d : prf nil p) : prf Γ (◻p)

axiom ax {Γ : ctx} {p : form} : prf (Γ ⸴ p) p

notation `·` := nil
notation Γ `⊢ₖ` p := prf Γ p
notation α `⇒` β := α → β 

def deduction {Γ : ctx} (p q : form) :
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

-- Maybe I can group up the following 'begin ... end' block and encapsulate it in a new tactic?

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

/- Kripke models -/

definition wrld : Type := nat

definition access : Type := wrld → wrld → bool

definition val : Type := wrld → var → bool

notation `𝓦` := wrld 
notation `𝓡` := access
notation `𝓿` := val 

-- Still incomplete:

def intrpr : form → (𝓦 × 𝓡 × 𝓿) → bool
| (form.atom v) := λ M, nat.rec_on M.fst tt (λ w IH, band IH (M.snd.snd w v))
| ~ p           := λ M, bnot (intrpr p M)
| (p ⊃ q)       := λ M, bor (intrpr p M) (bnot (intrpr q M)) 
| ◻ p          := λ M, nat.rec_on M.fst tt (λ w IH, _ )

end mpl
