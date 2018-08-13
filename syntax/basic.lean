/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .language.basic .context.basic

open list nat bool

/- the K system -/

inductive prf : ctx → form → Prop
| pl1 {Γ : ctx} {p q : form} : prf Γ (p ⊃ (q ⊃ p))
| pl2 {Γ : ctx} {p q r : form} : prf Γ ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))
| pl3 {Γ : ctx} {p q : form} :  prf Γ (((~p) ⊃ ~q) ⊃ (((~p) ⊃ q) ⊃ p))
| mp {Γ : ctx}  {p q : form} (d₁: prf Γ (p ⊃ q)) (d₂ : prf Γ p) : prf Γ q
| k {Γ : ctx}  {p q : form} : prf Γ ((◻(p ⊃ q)) ⊃ ((◻p) ⊃ (◻q)))
| nec {Γ : ctx} {p : form} (d : prf nil p) : prf Γ (◻p)

axiom ax {Γ : ctx} {p : form} (d : p ∈ Γ) : prf Γ p

notation Γ `⊢ₖ` p := prf Γ p
notation α `⇒` β := α → β 
