/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..default

open form classical

@[reducible]
def wrld (σ : nat) : Type := ctx σ

variable {σ : nat}

/- Kripke models for intuitionistic logic -/

structure model :=  (wrlds : set (wrld σ)) (access : wrld σ → wrld σ → bool) (val : var σ → wrld σ → bool) 
                    (refl : ∀ w ∈ wrlds, access w w = tt) (trans : ∀ w ∈ wrlds, ∀ v ∈ wrlds, ∀ u ∈ wrlds, access w v = tt → access v u = tt → access w u = tt)

notation `𝓦` `⸴` `𝓡` `⸴` `𝓿` := model

notation `𝓦` `▹` M := M.wrlds
notation `𝓡` `▹` M := M.access
notation `𝓿` `▹` M := M.val

local attribute [instance] prop_decidable

noncomputable def form_tt_in_wrld (M : 𝓦 ⸴ 𝓡 ⸴ 𝓿) : form σ → wrld σ → bool
|  (#p)   := λ w, (𝓿 ▹ M) p w
| (bot _) := λ w, ff
| (p & q) := λ w, (form_tt_in_wrld p w) && (form_tt_in_wrld q w)
| (p ∨ q) := λ w, (form_tt_in_wrld p w) || (form_tt_in_wrld q w)
| (p ⊃ q) := λ w, 
  if (∀ v, w ∈ (𝓦 ▹ M) → v ∈ (𝓦 ▹ M) → (𝓡 ▹ M) w v = tt → (form_tt_in_wrld p v = tt) → (form_tt_in_wrld q v = tt)) then tt else ff

/- Satisfiability -/

notation M `⦃` p `⦄` w := form_tt_in_wrld M p w

@[reducible]
def is_persistent (M : 𝓦 ⸴ 𝓡 ⸴ 𝓿) : Prop := ∀ {p : var σ}, ∀ w ∈ (𝓦 ▹ M), ∀ v ∈ (𝓦 ▹ M), ((𝓡 ▹ M) w v = tt) → ((M⦃#p⦄w) = tt) → ((M⦃#p⦄v) = tt)

inductive stsf (M : 𝓦 ⸴ 𝓡 ⸴ 𝓿) (p : form σ) : Prop 
| is_true (m : Π w ∈ (𝓦 ▹ M), (M ⦃p⦄ w) = tt) (per : is_persistent M) : stsf

-- 

notation M `⊨ᵢ` p := stsf M p

/- Validity -/

local attribute [instance] classical.prop_decidable

noncomputable def ctx_tt_in_wrld (M : 𝓦 ⸴ 𝓡 ⸴ 𝓿) (Γ : ctx σ) : wrld σ → bool :=
assume w, if (∀ p, p ∈ Γ → form_tt_in_wrld M p w = tt) then tt else ff

notation M `⦃`Γ`⦄` w := ctx_tt_in_wrld M Γ w

inductive sem_csq (Γ : ctx σ) (p : form σ) : Prop
| is_true (m : ∀ (M : 𝓦 ⸴ 𝓡 ⸴ 𝓿), ∀ w ∈ (𝓦 ▹ M), is_persistent M → ((M ⦃Γ⦄ w) = tt) → (M ⦃p⦄ w) = tt) : sem_csq

notation Γ `⊨ᵢ` p := sem_csq Γ p