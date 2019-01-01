/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import data.equiv.encodable .default

open form nat list decidable 

variables {σ : nat}

/- encoding of propositional formulas -/

-- to merge language with pl later

instance of_form : encodable (form σ) :=
sorry

def no_code_is_zero : ∀ p : form σ, encodable.encode p ≥ 1 := sorry
