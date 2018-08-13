/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..default

/- Kripke models -/

definition frame : Type := (nat × (nat → nat → bool))

definition k_model : Type := frame × (nat → nat → bool)

notation `𝓦` `⸴` `𝓡` `⸴` `𝓿` := k_model

def true_in_wrld (M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)) : form → nat → bool
| # p     := λ w, M.snd w p --nat.rec_on (M.fst.fst) tt (λ _ _, M.snd w p)
| ~ p     := λ w, bnot (true_in_wrld p w)
| (p ⊃ q) := λ w, (bnot (true_in_wrld p w)) || (true_in_wrld q w) 
| ◻ p    := λ w, 
    nat.rec_on M.fst.fst tt 
    (λ v IH, IH && ((bnot (M.fst.snd w v)) || (true_in_wrld p v)))

notation M `⦃`p`⦄` w := true_in_wrld M p w

-- W wrld is a n ∈ nat s.t. w ∈ wrld iff w ≤ wrld
