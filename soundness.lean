/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen

Soundness for K
-/

import .semantics.default .semantics.kripke.lemmas

/- (Weak) Soundness -/

inductive stsf (M : (𝓦 ⸴ 𝓡 ⸴ 𝓿) ) (p : form) : Prop 
| is_true (m : Π (w : nat),  (M ⦃p⦄ w) = tt ) : stsf
notation M `⊨ₖ` p := stsf M p

definition wk_sndnss (p : form) (M : (𝓦 ⸴ 𝓡 ⸴ 𝓿) ) :
( · ⊢ₖ p) ⇒ (M ⊨ₖ p) :=
begin
  intro H,
  induction H,
    repeat {
      apply stsf.is_true,
        intros w,
        unfold true_in_wrld,
        induction (true_in_wrld M H_p w), 
          induction (true_in_wrld M H_q w),
            simp, simp,
          induction (true_in_wrld M H_q w),
            simp, simp
    },
          induction (true_in_wrld M H_r w),
            simp, simp,
    
    apply stsf.is_true,
      induction H_ih_d₁, 
        induction H_ih_d₂,
          intros w,
          apply eq.symm,
            exact (
              calc 
                tt  = M⦃H_p ⊃ H_q⦄w  : eq.symm (H_ih_d₁ w)
                ... = bnot (M⦃H_p⦄w)  || M⦃H_q⦄w  : rfl
                ... = ff  || M⦃H_q⦄w  : eq.substr (H_ih_d₂ w) rfl
                ... = M⦃H_q⦄w  : ff_bor _
            ),
    apply stsf.is_true,
      intro w,
      apply impl_tt_to_impl,
        intro H,
        apply impl_tt_to_impl,
          apply nec_impl_to_nec_impl_nec,
            assumption,
    apply stsf.is_true,
      intro w, 
      unfold true_in_wrld,
      induction H_ih,
        induction M.fst.fst with k IH,
          simp, simp,
          apply and.intro,
            exact IH,
            induction ((M.fst).snd w k), 
              simp, simp,
              exact (H_ih k)
end

/- (Strong) Soundness -/

def ctx.true_in_wrld (M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)) : ctx → nat → bool
| ·      := λ w, tt
| (Γ ⸴ p) := λ w, ctx.true_in_wrld Γ w && M⦃p⦄w

notation M `⦃`p`⦄` w := ctx.true_in_wrld M p w

inductive sem_csq (Γ : ctx) (p : form) : Prop
| is_true (m : Π (M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)) (w : nat), (M ⦃Γ⦄ w) = tt → (M ⦃p⦄ w) = tt ) : sem_csq

notation Γ `⊨ₖ` p := sem_csq Γ p

definition sndnss (M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)) (Γ : ctx) (p q : form)  :
  (Γ ⊢ₖ p) ⇒ (Γ ⊨ₖ p) :=
begin
  intro H,
  induction H,
    repeat {
      apply sem_csq.is_true,
        intros M w csq,
        unfold true_in_wrld ctx.true_in_wrld,
        induction (true_in_wrld M H_p w), 
          induction (true_in_wrld M H_q w),
            simp, simp,
          induction (true_in_wrld M H_q w),
            simp, simp
    },
          induction (true_in_wrld M H_r w),
            simp, simp,
        
      apply sem_csq.is_true,
      induction H_ih_d₁, 
        induction H_ih_d₂,
        intros M w csq,
          apply eq.symm,
            exact (
              calc 
                tt  = M⦃H_p ⊃ H_q⦄w  : eq.symm (H_ih_d₁ M w csq)
                ... = bnot (M⦃H_p⦄w)  || M⦃H_q⦄w  : rfl
                ... = ff  || M⦃H_q⦄w  : eq.substr (H_ih_d₂ M w csq) rfl
                ... = M⦃H_q⦄w  : ff_bor _
            ),

      apply sem_csq.is_true,
        intros M w csq,
        apply impl_tt_to_impl,
          intro H,
          apply impl_tt_to_impl,
            apply nec_impl_to_nec_impl_nec,
              assumption,

      apply sem_csq.is_true,
        intros M w csq,
        unfold true_in_wrld ctx.true_in_wrld,
      induction H_ih,
        induction M.fst.fst with k IH,
          simp, simp,
          apply and.intro,
            exact IH,
            induction ((M.fst).snd w k), 
              simp, simp,
              exact (H_ih M k rfl)
end
