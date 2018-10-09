/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..language.basic

variable (σ : nat)

/- context -/ 

def ctx : Type := set (form σ)

notation `·` := {}
notation Γ `⸴` p := set.insert p Γ
notation Γ `⊔` Δ := set.union Γ Δ

instance : has_mem (form σ) (ctx σ) := ⟨set.mem⟩

instance : has_subset (ctx σ) := ⟨set.subset⟩

instance : has_sep (form σ) (ctx σ) := ⟨set.sep⟩

instance : has_emptyc (ctx σ) := ⟨λ a, false⟩

instance : has_insert (form σ) (ctx σ) := ⟨set.insert⟩
