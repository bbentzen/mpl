/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .language

/- context -/ 

@[reducible]
def ctx (σ : nat) : Type := set (form σ)

notation `·` := {}
notation Γ ` ⸴ ` p := set.insert p Γ