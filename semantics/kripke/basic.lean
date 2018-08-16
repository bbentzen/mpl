/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..default

open classical

/- Kripke models -/

definition frame : Type := (list nat) × (nat → nat → Prop)

definition k_model : Type := frame × (nat → nat → Prop)

notation `𝓦` `⸴` `𝓡` `⸴` `𝓿` := k_model

def true_in_wrld (M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)) : form → nat → Prop
| # p     := λ w, M.snd w p
| ~ p     := λ w, ¬ (true_in_wrld p w)
| (p ⊃ q) := λ w, (true_in_wrld p w) → (true_in_wrld q w) 
| ◻ p    := λ w, 
  (∀ v : nat, (v ∈ M.fst.fst) → (M.fst.snd w v) → (true_in_wrld p v))

notation M `⦃`p`⦄` w := true_in_wrld M p w
