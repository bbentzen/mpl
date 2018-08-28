/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .language.basic .context.basic

variable {σ : nat}

inductive prf (Γ : ctx σ) : form σ → Prop
| ax  {p : form σ} (h : p ∈ Γ) : prf p
| pl1 {p q : form σ} : prf (p ⊃ (q ⊃ p))
| pl2 {p q r : form σ} : prf ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))
| pl3 {p q : form σ} :  prf (((~p) ⊃ ~q) ⊃ (((~p) ⊃ q) ⊃ p))
| mp  {p q : form σ} (hpq: prf (p ⊃ q)) (hp : prf p) : prf q

notation Γ `⊢ₚ` p := prf Γ p
notation Γ `⊬ₚ` p := prf Γ p → false

/- metaconnectives -/

notation α `⇒` β := α → β 
notation α `⇔` β := α ↔ β 
