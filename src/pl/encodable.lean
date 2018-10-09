/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .syntax.language.basic

open nat

variables {σ : nat}

/- enumeration of all propositional atoms -/

class encodable (α : Type*) :=
(encode : α → nat) (decode : nat → option α) (encodek : ∀ a, decode (encode a) = some a)

-- TODO: --import factors and other operations from mathlib

instance of_form : encodable (form σ) := sorry

def no_code_is_zero : ∀ p : form σ, encodable.encode p ≥ 1 := sorry 

/-
def encode_form : form σ → nat
|  (#v) := 3^(v.1 + 1)
|   ⊥    := 2
| (p ⊃ q) := 5^(encode_form p) * 7^(encode_form q)

noncomputable def no_of_occurr : list nat → nat → nat
| []     b := 0
| (a::l) b := if a = b then no_of_occurr l b + 1 else no_of_occurr l b

def decode_atom (n : nat) : Prop :=
list.rec_on (factors n) true (λ n _ ih, if n = 2 then ih else false)

def decode_impl (n : nat) : Prop :=
list.rec_on (factors n) true (λ n _ ih, if n ≠ 3 ∨ n ≠ 5 then false else ih)

noncomputable def decode_form : nat → option (form σ)
|   0   := none 
|   1   := none 
|   2   := some ⊥
| (k+3) := let n := k+3 in
  if decode_atom n then dite (pred (no_of_occurr (factors n) 3) < σ) (λ h , option.some (#⟨_,h⟩ )) (λ _, none) else
  if decode_impl n then option.some (_ ⊃ _) -- decode (no_of_occurr (factors n) 5)
  else none
-/