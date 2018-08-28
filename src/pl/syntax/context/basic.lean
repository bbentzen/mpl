/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..language.basic ..misc

variable σ : nat

/- context -/ 

def ctx : Type := list (form σ)

notation `·` := list.nil
notation Γ `⸴` p := list.cons p Γ
notation Γ `⊔` Δ := list.append Γ Δ
notation `{` p `}` := [p]  

instance : has_mem (form σ) (ctx σ) := ⟨list.mem⟩

instance : has_subset (ctx σ) := ⟨list.subset⟩
