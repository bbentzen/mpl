/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..default

variable (σ : nat)

def true_in_val (v : var σ → bool) : form σ → bool
| (#p) := v p
|   ⊥    := ff
| (p ⊃ q) := (bnot (true_in_val p)) || (true_in_val q) 

/- Satisfiability -/

notation `⦃`p`⦄` v := true_in_val _ v p

/- Validity -/

def ctx.true_in_val (v : var σ → bool) : ctx σ → bool
| ·      := tt
| (Γ ⸴ p) := ctx.true_in_val Γ && ⦃p⦄v

notation `⦃`Γ`⦄` v := ctx.true_in_val _ v Γ

inductive sem_csq (Γ : ctx σ) (p : form σ) : Prop
| is_true (m : Π (v : var σ → bool), ((⦃Γ⦄ v) = tt) → (⦃p⦄ v) = tt) : sem_csq

notation Γ `⊨ₚ` p := sem_csq _ Γ p
