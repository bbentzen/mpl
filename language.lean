/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

namespace mpl
open list nat

/- language -/

inductive form : Type
| var : nat → form
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
| nec {p : form} (d : prf nil p) : prf nil (◻p)

axiom ax {Γ : ctx} {p : form} : prf (Γ ⸴ p) p

notation `·` := nil
notation Γ `⊢ₖ` p := prf Γ p
notation α `⇒` β := α → β 

def deduction (p q : form) :
  ({p} ⊢ₖ q) ⇒ (· ⊢ₖ p ⊃ q) :=
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

end mpl
