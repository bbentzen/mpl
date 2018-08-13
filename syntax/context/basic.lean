/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..language.basic

/- definition -/ 

def ctx : Type := list form

notation `·` := list.nil
notation Γ `⸴` p := list.cons p Γ
notation Γ `∪` Ψ := append Γ Ψ
notation `{` p `}` := [p]  

instance : has_mem form ctx := ⟨list.mem⟩
