/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .syntax.lemmas .semantics.lemmas 

variable {σ : nat}

/- soundness -/

theorem sndnss {Γ : ctx σ} {p : form σ} :
  (Γ ⊢ₛ₅ p) → (Γ ⊨ₛ₅ p) :=
begin
  intro h,
  induction h,
  { apply sem_csq.is_true,
    intros, apply ctx_tt_to_mem_tt,
    repeat {assumption} },

  { apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_pl1 },

  { apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_pl2 },

  { apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_pl3 },

    { apply sem_csq.is_true,
      induction h_ih_hpq,
      induction h_ih_hp,
      intros M w wmem ctt,
      revert h_ih_hpq,
      unfold forces_form, simp,
      intro hpq,
      cases (hpq M w wmem ctt),
      { assumption },
      { exfalso,
        apply tt_eq_ff_eq_false,
        rw eq.symm (h_ih_hp M w wmem ctt),
        assumption } },
      
    { apply sem_csq.is_true,
      intros M w wmem ctt, 
      apply is_true_k },

    { apply sem_csq.is_true,
      intros M w wmem ctt,
      apply is_true_t,
      repeat {assumption} },

    { apply sem_csq.is_true,
      intros M w wmem ctt,
      apply is_true_s4 },
      
    { apply sem_csq.is_true,
      intros M w wmem ctt,
      apply is_true_b },

    { apply sem_csq.is_true,
      intros M w wmem ctt,
      unfold forces_form, simp,
      induction h_ih,
      intros v vmem wmem rwv,
      apply h_ih, assumption,
      apply empty_ctx_tt }
end