/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..default

variable {σ : nat}

inductive prf (Γ : ctx σ) : form σ → Prop
| ax  {p : form σ} (h : p ∈ Γ) : prf p
| pl1 {p q : form σ} : prf (p ⊃ (q ⊃ p))
| pl2 {p q r : form σ} : prf ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))
| andr {p q : form σ} : prf ((p & q) ⊃ p)
| andl {p q : form σ} : prf ((p & q) ⊃ q)
| andi {p q : form σ} : prf (p ⊃ (q ⊃ (p & q)))
| orr {p q : form σ} : prf (p ⊃ (p ∨ q))
| orl {p q : form σ} : prf (q ⊃ (p ∨ q))
| ore {p q r : form σ} : prf ((p ⊃ r) ⊃ ((q ⊃ r) ⊃ ((p ∨ q) ⊃ r)))
| falso {p : form σ} :  prf (⊥ ⊃ p)
| mp  {p q : form σ} (hpq: prf (p ⊃ q)) (hp : prf p) : prf q

notation Γ `⊢ᵢ` p := prf Γ p
notation Γ `⊬ᵢ` p := prf Γ p → false

/- metaconnectives -/

notation α `⇒` β := α → β 
notation α `⇔` β := α ↔ β 