/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic

open form

variable {σ : nat}

/- general facts about the logical constants -/

def neg_tt_iff_ff {v : var σ → bool} {p : form σ} :
  (⦃~p⦄v) = tt ↔ (⦃p⦄v) = ff :=
by unfold form_tt_in_val; induction (form_tt_in_val v p); simp; simp

def neg_ff_iff_tt {v : var σ → bool} {p : form σ} :
  (⦃~p⦄v) = ff ↔ (⦃p⦄v) = tt :=
by unfold form_tt_in_val; induction (form_tt_in_val v p); simp; simp

def impl_tt_iff_tt_implies_tt {v : var σ → bool} {p q : form σ} :
  (⦃p ⊃ q⦄v) = tt ↔ ((⦃p⦄v) = tt → (⦃q⦄v) = tt) :=
by unfold form_tt_in_val; induction (form_tt_in_val v p); repeat { induction (form_tt_in_val v q), simp, simp }

def impl_tt_iff_ff_or_tt {v : var σ → bool} {p q : form σ} :
  (⦃p ⊃ q⦄v) = tt ↔ ((⦃p⦄v) = ff ∨ (⦃q⦄v) = tt) :=
by unfold form_tt_in_val; induction (form_tt_in_val v p); repeat { induction (form_tt_in_val v q), simp, simp }

def impl_ff_iff_tt_and_tt {v : var σ → bool} {p q : form σ} :
  (⦃p ⊃ q⦄v) = ff ↔ ((⦃p⦄v) = tt ∧ (⦃q⦄v) = ff) :=
by unfold form_tt_in_val; induction (form_tt_in_val v p); repeat { induction (form_tt_in_val v q), simp, simp }

def bot_is_insatisf : 
  ¬ ∃ (v : var σ → bool), (⦃bot σ⦄ v) = tt :=
by intro h; cases h; exact (bool.no_confusion h_h) 

/- general facts about contexts -/ 

def ctx_tt_iff_mem_tt {Γ : ctx σ} {v : var σ → bool} :
  (⦃Γ⦄v) = tt ↔ (∀ p, p ∈ Γ → (⦃p⦄v) = tt) :=
begin
  unfold ctx_tt_in_val,
  induction (classical.prop_decidable _),
      apply iff.intro,
          simp, intro,
          simp, assumption,
          simp
end

def mem_tt_to_ctx_tt (Γ : ctx σ) {v : var σ → bool} :
 (∀ (p : form σ) (h : p ∈ Γ), (⦃p⦄ v) = tt) → (⦃Γ⦄ v) = tt :=
ctx_tt_iff_mem_tt.2

def ctx_tt_to_mem_tt {Γ : ctx σ} {p : form σ} {v : var σ → bool} :
  (⦃Γ⦄v) = tt → p ∈ Γ → (⦃p⦄v) = tt :=
by intro; apply ctx_tt_iff_mem_tt.1; assumption

/- context projections -/

def cons_ctx_tt_iff_and {Γ : ctx σ} {p : form σ} {v : var σ → bool} :
  (⦃(Γ ⸴ p)⦄v) = tt ↔ (⦃Γ⦄v) = tt ∧ (⦃p⦄v) = tt :=
begin
  unfold ctx_tt_in_val,
  induction (classical.prop_decidable (∀ p, p ∈ Γ → form_tt_in_val v p = tt)),
    simp, apply iff.intro,
      intro h', apply false.rec, apply h,
        intros q qmem, apply h',
          apply mem_ext_cons_left, assumption,
      intro h', cases h', intros q qmem,
        cases qmem,
          induction qmem, assumption,
          apply h'_left, assumption,

    simp, apply iff.intro,
      intro h', split,
        assumption,
        apply h', apply trivial_mem_left,
      intros h' q qmem,
        cases h', cases qmem,
          induction qmem, assumption,
          apply h'_left, assumption,
end

def cons_ctx_tt_to_ctx_tt {Γ : ctx σ} {p : form σ} {v : var σ → bool} :
  (⦃(Γ ⸴ p)⦄v) = tt → (⦃Γ⦄v) = tt :=
by intro h; apply and.elim_left; apply cons_ctx_tt_iff_and.1 h

def ctx_tt_cons_tt_to_cons_ctx_tt {Γ : ctx σ} {p : form σ} {v : var σ → bool} :
  (⦃Γ⦄v) = tt → (⦃p⦄v) = tt  → (⦃(Γ ⸴ p)⦄v) = tt :=
by intros hg hp; apply cons_ctx_tt_iff_and.2; split; assumption; assumption

/- sub-contexts -/

def ctx_tt_to_subctx_tt {Γ Δ : ctx σ} {v : var σ → bool} :
  (⦃Γ⦄v) = tt → Δ ⊆ Γ → (⦃Δ⦄v) = tt :=
begin
  intros h s, 
    apply ctx_tt_iff_mem_tt.2, 
      intros p pmem,
         apply ctx_tt_iff_mem_tt.1 h,
           apply s, exact pmem
end

/- useful metatheorems -/

def sem_deduction {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⊨ₚ q) → (Γ ⊨ₚ p ⊃ q) :=
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
  (Γ ⊨ₚ p) → (Γ ⸴ q ⊨ₚ p) :=
begin
  intro h,
    cases h,
      apply sem_csq.is_true,
        intros v ant,
          apply h,
            exact (cons_ctx_tt_to_ctx_tt ant)
end
