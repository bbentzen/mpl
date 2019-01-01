/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/

import ..encodable2 .language 

-- A more concise encoding of form -- Thanks Jeremy!

namespace form

private def constructors (σ : nat) := (var σ) ⊕ unit ⊕ unit ⊕ unit

local notation `catom` v := sum.inl v
local notation `cbot`    := sum.inr (sum.inl unit.star)
local notation `cimpl`   := sum.inr (sum.inr (sum.inr unit.star))
local notation `cbox`    := sum.inr (sum.inr (sum.inl unit.star))

@[simp]
private def arity (σ : nat) : constructors σ → nat
| (catom v) := 0
| cbot      := 0
| cimpl     := 2
| cbox      := 1

variable {σ : nat}

private def f : form σ → Wfin (arity σ) 
| (atom v)   := ⟨catom v, fin.mk_fn0⟩
| (bot _)    := ⟨cbot, fin.mk_fn0⟩
| (impl p q) := ⟨cimpl, fin.mk_fn2 (f p) (f q)⟩       
| (box  p)   := ⟨cbox, fin.mk_fn1 (f p)⟩

private def finv : Wfin (arity σ) → form σ
| ⟨catom a, fn⟩ := atom a 
| ⟨cbot, fn⟩    := bot _
| ⟨cimpl, fn⟩   := impl (finv (fn ⟨0, dec_trivial⟩)) (finv (fn ⟨1, dec_trivial⟩))       
| ⟨cbox, fn⟩    := box  (finv (fn ⟨0, dec_trivial⟩))        

instance [encodable (var σ)] : encodable (form σ) :=
begin
  haveI : encodable (constructors σ) :=
    by { unfold constructors, apply_instance },
  exact encodable.of_left_inverse f finv 
    (by { intro p, induction p; simp [f, finv, *] })
end

end form
