/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .syntax.lemmas .semantics.lemmas

variable {σ : nat}

/- soundness -/

definition sndnss {Γ : ctx σ} {p : form σ} :
  (Γ ⊢ᵢ p) ⇒ (Γ ⊨ᵢ p) :=
begin
  intro h,
  induction h,
    apply sem_csq.is_true,
      intros,
        apply ctx_tt_to_mem_tt,
          repeat {assumption},
    repeat {
      apply sem_csq.is_true,
        intros M w h_w h_per ctt,
        apply pl1_tt w h_w <|> apply pl2_tt w h_w,
        assumption,
    },
    apply sem_csq.is_true,
      intros M w h_w h_per ctt,
        apply forall_wrlds_to_impl_tt, assumption, intros,
          unfold form_tt_in_wrld at a_1, simp at a_1,
          apply and.elim_left <|> apply and.elim_right,
          assumption,

    apply sem_csq.is_true,
      intros M w h_w h_per ctt,
        apply forall_wrlds_to_impl_tt, assumption, intros,
          unfold form_tt_in_wrld at a_1, simp at a_1,
          apply and.elim_right,
          assumption,
    
    apply sem_csq.is_true,
      intros M w h_w h_per ctt,
        apply forall_wrlds_to_impl_tt, assumption, intros,
          apply forall_wrlds_to_impl_tt, assumption, intros,
            unfold form_tt_in_wrld, simp,
            split, apply per_in_wrld, assumption, exact H, repeat {assumption}, 
    
    apply sem_csq.is_true,
      intros M w h_w h_per ctt,
        apply forall_wrlds_to_impl_tt, assumption, intros,
          unfold form_tt_in_wrld, simp,
          left, assumption,
    
    apply sem_csq.is_true,
      intros M w h_w h_per ctt,
        apply forall_wrlds_to_impl_tt, assumption, intros,
          unfold form_tt_in_wrld, simp,
          right, assumption,

    apply sem_csq.is_true,
      intros M w h_w h_per ctt,
        apply forall_wrlds_to_impl_tt, assumption, intros,
          apply forall_wrlds_to_impl_tt, assumption, intros,
            apply forall_wrlds_to_impl_tt, assumption, intros,
              unfold form_tt_in_wrld at a_5, simp at a_5, cases a_5,
                apply impl_tt_to_tt_impl_tt, assumption,
                apply per_in_wrld, assumption, exact H_1, assumption, assumption,
                  apply per_in_wrld, assumption, exact H, repeat {assumption},
                apply impl_tt_to_tt_impl_tt, assumption,
                  apply per_in_wrld, assumption, exact H_1, repeat {assumption},
    
    apply sem_csq.is_true,
      intros M w h_w h_per ctt,
        apply forall_wrlds_to_impl_tt, assumption, intros,
          unfold form_tt_in_wrld at a_1, simp at a_1, contradiction,

    apply sem_csq.is_true,
        intros M w h_w h_per ctt,
        cases h_ih_hpq, cases h_ih_hp,
          apply impl_tt_to_tt_impl_tt, assumption,
            apply h_ih_hpq, repeat {assumption},
            apply h_ih_hp, repeat {assumption},
            
end
