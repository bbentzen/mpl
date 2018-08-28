/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic

variable {σ : nat}

/- general facts about the logical constants -/

def neg_tt_iff_ff {v : var σ → bool} {p : form σ} :
  (⦃~p⦄v) = tt ⇔ (⦃p⦄v) = ff :=
by unfold true_in_val; induction (true_in_val _ v p); simp; simp

def neg_ff_iff_tt {v : var σ → bool} {p : form σ} :
  (⦃~p⦄v) = ff ⇔ (⦃p⦄v) = tt :=
by unfold true_in_val; induction (true_in_val _ v p); simp; simp

def impl_tt_iff_tt_implies_tt {v : var σ → bool} {p q : form σ} :
  (⦃p ⊃ q⦄v) = tt ⇔ ((⦃p⦄v) = tt ⇒ (⦃q⦄v) = tt) :=
by unfold true_in_val; induction (true_in_val _ v p); repeat { induction (true_in_val _ v q), simp, simp }

def impl_tt_iff_ff_or_tt {v : var σ → bool} {p q : form σ} :
  (⦃p ⊃ q⦄v) = tt ⇔ ((⦃p⦄v) = ff ∨ (⦃q⦄v) = tt) :=
by unfold true_in_val; induction (true_in_val _ v p); repeat { induction (true_in_val _ v q), simp, simp }

def impl_ff_iff_tt_and_tt {v : var σ → bool} {p q : form σ} :
  (⦃p ⊃ q⦄v) = ff ⇔ ((⦃p⦄v) = tt ∧ (⦃q⦄v) = ff) :=
by unfold true_in_val; induction (true_in_val _ v p); repeat { induction (true_in_val _ v q), simp, simp }


def bot_is_insatisf : 
  ¬ ∃ (v : var σ → bool), (⦃⊥⦄ v) = tt :=
by intro h; cases h; exact (bool.no_confusion h_h) 

/- context projections -/

def cons_ctx_tt_iff_and {Γ : ctx σ} {p : form σ} {v : var σ → bool} :
  (⦃(Γ ⸴ p)⦄v) = tt ⇔ (⦃Γ⦄v) = tt ∧ (⦃p⦄v) = tt :=
by unfold ctx.true_in_val; induction (ctx.true_in_val _ v Γ); repeat { induction (true_in_val _ v p), simp, simp }

def cons_ctx_tt_to_ctx_tt {Γ : ctx σ} {p : form σ} {v : var σ → bool} :
  (⦃(Γ ⸴ p)⦄v) = tt ⇒ (⦃Γ⦄v) = tt :=
by intro h; apply and.elim_left; apply cons_ctx_tt_iff_and.1 h

def ctx_tt_cons_tt_to_cons_ctx_tt {Γ : ctx σ} {p : form σ} {v : var σ → bool} :
  (⦃Γ⦄v) = tt ⇒ (⦃p⦄v) = tt  ⇒ (⦃(Γ ⸴ p)⦄v) = tt :=
begin
  unfold ctx.true_in_val,
  cases (true_in_val _ v p),
    simp, simp,
  apply id
end

/- more general facts -/ 

def ctx_tt_to_mem_tt {Γ : ctx σ} {p : form σ} {v : var σ → bool} :
  (⦃Γ⦄v) = tt ⇒ p ∈ Γ ⇒ (⦃p⦄v) = tt :=
begin
  intros h memp, induction Γ, revert memp, simp,
  cases memp,
    induction memp, apply and.elim_right, apply cons_ctx_tt_iff_and.1 h,
    apply Γ_ih, apply and.elim_left, apply cons_ctx_tt_iff_and.1 h, exact memp
end

def ctx_tt_to_subctx_tt {Γ Δ : ctx σ} {v : var σ → bool} :
  (⦃Γ⦄v) = tt ⇒ Δ ⊆ Γ ⇒ (⦃Δ⦄v) = tt :=
begin
  intros h s,
  induction Δ,
    reflexivity, simp at *,
    apply cons_ctx_tt_iff_and.2, simp, split,
      apply Δ_ih, apply sub_cons_is_sub s,
      apply ctx_tt_to_mem_tt h,
        apply s trivial_mem_left
end

def mem_tt_to_ctx_tt (Γ : ctx σ) {v : var σ → bool} :
 (∀ (p : form σ) (h : p ∈ Γ), (⦃p⦄ v) = tt) ⇒ (⦃Γ⦄ v) = tt :=
begin
  intro, induction Γ, reflexivity,
  apply tt_and_tt_to_band_tt,
    apply and.intro,
      apply Γ_ih,
        intros p pmem, apply a,
        apply or.intro_right, exact pmem,
      apply a,
        apply or.intro_left, reflexivity
end

/- useful metatheorems -/

def sem_deduction {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⊨ₚ q) ⇒ (Γ ⊨ₚ p ⊃ q) :=
begin
 intro h,
 cases h,
   apply sem_csq.is_true,
     intros v ant,
     apply impl_tt_iff_tt_implies_tt.2,
       intro hp,
       apply h,
         apply ctx_tt_cons_tt_to_cons_ctx_tt,
           exact ant,
           exact hp
end

def sum_weak {Γ : ctx σ} {p q r : form σ} :
  (Γ ⊨ₚ p) ⇒ (Γ ⸴ q ⊨ₚ p) :=
begin
  intro h,
    cases h,
      apply sem_csq.is_true,
        intros v ant,
          apply h,
            exact (cons_ctx_tt_to_ctx_tt ant)
end
