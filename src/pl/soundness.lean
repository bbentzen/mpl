/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .semantics.basic .misc

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
        induction Γ,
          revert h_h, simp,
          cases h_h,
            induction h_h,
              apply and.elim_right,
                apply band_tt_to_tt_and_tt,
                  exact ant,
            apply Γ_ih,
              exact h_h,
              apply and.elim_left,
                apply band_tt_to_tt_and_tt,
                  exact ant,
    repeat {
      apply sem_csq.is_true,
        intros v ant,
        unfold true_in_val ctx.true_in_val,
        induction (true_in_val _ v h_p), 
          induction (true_in_val _ v h_q),
            simp, simp,
          induction (true_in_val _ v h_q),
            simp, simp
    },
          induction (true_in_val _ v h_r),
            simp, simp,

      apply sem_csq.is_true,
      induction h_ih_hpq, 
        induction h_ih_hp,
        intros v ant,
        have h1 : (bnot (true_in_val _ v h_p) || true_in_val _ v h_q) = tt :=
           h_ih_hpq v ant,
        have h2 : true_in_val _ v h_p = tt := 
           h_ih_hp v ant, 
        revert h1 h2,
        induction (true_in_val _ v h_p),
          repeat {
            induction (true_in_val _ v h_q),
            simp, simp
          }
end
