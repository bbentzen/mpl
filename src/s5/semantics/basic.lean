/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..default

open form classical

@[reducible] def wrld (σ : nat) := ctx σ

variable {σ : nat}

/- Kripke models -/

structure model := (wrlds : set (wrld σ)) (access : wrld σ → wrld σ → bool) (val : fin σ → wrld σ → bool)
                   (refl : ∀ w ∈ wrlds, access w w = tt)
                   (symm : ∀ w ∈ wrlds, ∀ v ∈ wrlds, access w v  = tt → access v w  = tt)
                   (trans : ∀ w ∈ wrlds, ∀ v ∈ wrlds, ∀ u ∈ wrlds, access w v  = tt → access v u  = tt → access w u  = tt)

local attribute [instance] prop_decidable

noncomputable def forces_form (M : model) : form σ → wrld σ → bool
|  (#p)   := λ w, M.val p w
| (bot σ) := λ w, ff 
| (p ⊃ q) := λ w, (bnot (forces_form p w)) || (forces_form q w) 
|  (◻p)   := λ w,
  if (∀ v ∈ M.wrlds, w ∈ M.wrlds → M.access w v = tt → forces_form p v = tt) then tt else ff

/- Forcing -/

notation w `⊩` `⦃` M `⦄ ` p := forces_form M p w

/- Local logical consequence -/

noncomputable def forces_ctx (M : model) (Γ : ctx σ) : wrld σ → bool :=
assume w, if (∀ p, p ∈ Γ → forces_form M p w = tt) then tt else ff

notation w `⊩` `⦃` M `⦄ ` p := forces_ctx M p w

inductive sem_csq (Γ : ctx σ) (p : form σ) : Prop
| is_true (m : ∀ (M : model) (w ∈ M.wrlds), ((w ⊩⦃M⦄ Γ) = tt) → (w ⊩⦃M⦄ p) = tt) : sem_csq

notation Γ ` ⊨ₛ₅ ` p := sem_csq Γ p