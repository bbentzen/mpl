/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .semantics.lemmas

variable {σ : nat}

/- soundness -/

definition sndnss {Γ : ctx σ} {p : form σ} :
  (Γ ⊢ₖ p) ⇒ (Γ ⊨ₖ p) :=
begin
  intro h,
  induction h,
    apply sem_csq.is_true,
      intros,
        apply ctx_tt_to_mem_tt,
          repeat {assumption},
    repeat {
      apply sem_csq.is_true,
        intros M w ctt,
        unfold form_tt_in_wrld,
          induction (form_tt_in_wrld M h_p w),
            repeat {
              induction (form_tt_in_wrld M h_q w),
                simp, simp,
            }
    },
          induction (form_tt_in_wrld M h_r w),
                simp, simp,
    apply sem_csq.is_true,
      induction h_ih_hpq,
        induction h_ih_hp,
          intros M w ctt,
            revert h_ih_hpq,
            unfold form_tt_in_wrld, simp,
            intro hpq,
            cases (hpq M w ctt),
             apply false.rec,
               exact (bool.no_confusion
                 (eq.trans (eq.symm (h_ih_hp M w ctt)) h)),
             assumption,
    apply sem_csq.is_true,
      intros M w ctt,
      apply impl_tt_iff_tt_implies_tt.2,
        intro lpq, apply impl_tt_iff_tt_implies_tt.2,
          revert lpq, unfold form_tt_in_wrld, simp,
          intros lpq lp v wmem vmem rwv,
            cases (lpq v wmem vmem rwv),
              exact (bool.no_confusion 
                (eq.trans (eq.symm (lp v wmem vmem rwv)) h)),
              assumption,
    apply sem_csq.is_true,
      induction h_ih,
        intros M w ctt,
        unfold form_tt_in_wrld, simp,
        intros v wmem vmem rwv,
          apply h_ih,
            apply eq.substr h_cnil,
              unfold ctx_tt_in_wrld,
              simp, intros, apply false.rec, assumption
end
