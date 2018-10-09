/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .semantics.lemmas .misc

variable {σ : nat}

open prf

/- soundness -/

definition sndnss {Γ : ctx σ} {p : form σ} :
  (Γ ⊢ₚ p) ⇒ (Γ ⊨ₚ p) :=
begin
  intro h,
  induction h,
    apply sem_csq.is_true,
      intros v ant,
        exact ctx_tt_to_mem_tt ant h_h,

    repeat {
        apply sem_csq.is_true,
          intros v ant,
          unfold form_tt_in_val ctx_tt_in_val,
          induction (form_tt_in_val v h_p), 
            induction (form_tt_in_val v h_q),
              simp, simp,
            induction (form_tt_in_val v h_q),
              simp, simp
    },
            induction (form_tt_in_val v h_r),
              simp, simp,

      apply sem_csq.is_true,
      induction h_ih_hpq, 
        induction h_ih_hp,
        intros v ant,
        have h1 : (bnot (form_tt_in_val v h_p) || form_tt_in_val v h_q) = tt :=
           h_ih_hpq v ant,
        have h2 : form_tt_in_val v h_p = tt := 
           h_ih_hp v ant, 
        revert h1 h2,
        induction (form_tt_in_val v h_p),
          repeat {
            induction (form_tt_in_val v h_q),
            simp, simp
          }
end
