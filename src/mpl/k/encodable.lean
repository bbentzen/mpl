/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .syntax.language.basic

open nat

variables {σ : nat}

/- enumeration of all propositions -/

class encodable (α : Type*) :=
(encode : α → nat) (decode : nat → option α) (encodek : ∀ a, decode (encode a) = some a)

-- TODO: --import factors and other operations from mathlib

instance of_form : encodable (form σ) := sorry

def no_code_is_zero : ∀ p : form σ, encodable.encode p ≥ 1 := sorry 