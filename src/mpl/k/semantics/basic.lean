/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..default

open classical

@[reducible]
def wrld (σ : nat) : Type := ctx σ

variable {σ : nat}

/- Kripke models -/

structure model := (wrlds : set (wrld σ)) (access : wrld σ → wrld σ → bool) (val : var σ → wrld σ → bool)

notation `𝓦` `⸴` `𝓡` `⸴` `𝓿` := model

notation `𝓦` `▹` M := M.wrlds
notation `𝓡` `▹` M := M.access
notation `𝓿` `▹` M := M.val

local attribute [instance] prop_decidable

noncomputable def form_tt_in_wrld (M : 𝓦 ⸴ 𝓡 ⸴ 𝓿) : form σ → wrld σ → bool
|  (#p)   := λ w, (𝓿 ▹ M) p w
|   ⊥     := λ w, ff 
| (p ⊃ q) := λ w, (bnot (form_tt_in_wrld p w)) || (form_tt_in_wrld q w) 
|  (◻p)   := λ w,
  if (∀ v, w ∈ (𝓦 ▹ M) → v ∈ (𝓦 ▹ M) → (𝓡 ▹ M) w v = tt → form_tt_in_wrld p v = tt) then tt else ff

/- Satisfiability -/

notation M `⦃` p `⦄` w := form_tt_in_wrld M p w

inductive stsf (M : 𝓦 ⸴ 𝓡 ⸴ 𝓿) (p : form σ) : Prop 
| is_true (m : Π w, (M ⦃p⦄ w) = tt) : stsf

notation M `⊨ₖ` p := stsf M p

/- Validity -/

local attribute [instance] classical.prop_decidable

noncomputable def ctx_tt_in_wrld (M : 𝓦 ⸴ 𝓡 ⸴ 𝓿) (Γ : ctx σ) : wrld σ → bool :=
assume w, if (∀ p, p ∈ Γ → form_tt_in_wrld M p w = tt) then tt else ff

notation M `⦃`Γ`⦄` w := ctx_tt_in_wrld M Γ w

inductive sem_csq (Γ : ctx σ) (p : form σ) : Prop
| is_true (m : Π (M : 𝓦 ⸴ 𝓡 ⸴ 𝓿) (w : wrld σ), ((M ⦃Γ⦄ w) = tt) → (M ⦃p⦄ w) = tt) : sem_csq

notation Γ `⊨ₖ` p := sem_csq Γ p
