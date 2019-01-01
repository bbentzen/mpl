/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..default

open form

variable {σ : nat}

def form_tt_in_val (v : var σ → bool) : form σ → bool
|  (#p)   := v p
| (bot σ) := ff
| (p ⊃ q) := (bnot (form_tt_in_val p)) || (form_tt_in_val q) 

/- Satisfiability -/

notation `⦃`p`⦄` v := form_tt_in_val v p

/- Validity -/

local attribute [instance] classical.prop_decidable

noncomputable def ctx_tt_in_val (v : var σ → bool) (Γ : ctx σ) : bool :=
 if (∀ p, p ∈ Γ → form_tt_in_val v p = tt) then tt else ff

notation `⦃`Γ`⦄` v := ctx_tt_in_val v Γ

inductive sem_csq (Γ : ctx σ) (p : form σ) : Prop
| is_true (m : Π (v : var σ → bool), ((⦃Γ⦄ v) = tt) → (⦃p⦄ v) = tt) : sem_csq

notation Γ `⊨ₚ` p := sem_csq Γ p
