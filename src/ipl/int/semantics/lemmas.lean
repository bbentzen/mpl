/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic

open form classical

variable {σ : nat}

def per_in_wrld {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} (v ∈ 𝓦 ▹ M) (w ∈ 𝓦 ▹ M) : 
  Π {p : form σ}, (is_persistent M) → (𝓡 ▹ M) w v = tt → ((M⦃p⦄w) = tt → (M⦃p⦄v) = tt)
|  (#p)   := begin intro h, apply h, assumption, assumption end 
| (bot _) := by intro; unfold form_tt_in_wrld; simp
| (p & q) := begin unfold form_tt_in_wrld, simp, intros, split, repeat {apply per_in_wrld, repeat {assumption}} end
| (p ∨ q) := begin unfold form_tt_in_wrld, simp, intros, cases a_2, left, apply per_in_wrld, repeat {assumption}, right, apply per_in_wrld, repeat {assumption} end
| (p ⊃ q) :=
  begin
    unfold form_tt_in_wrld, simp,
    intros _ rwv f v' hv hv' rvv' hpv',
    apply f, apply H, apply hv', apply M.trans w H v hv v' hv' rwv rvv', assumption
  end

/- general facts about some logical constants -/

def impl_tt_to_tt_impl_tt {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} (w ∈ 𝓦 ▹ M) {p q : form σ} :
  (M⦃p ⊃ q⦄w) = tt → ((M⦃p⦄w) = tt → (M⦃q⦄w) = tt) :=
begin
  unfold form_tt_in_wrld, simp,
  intros f hp, exact f w H H (M.refl w H) hp,
end

def forall_wrlds_to_impl_tt {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} (w ∈ 𝓦 ▹ M) {p q : form σ} :
  (∀ v ∈ (𝓦 ▹ M), (𝓡 ▹ M) w v = tt → (M⦃p⦄v) = tt → (M⦃q⦄v) = tt) → (M⦃p ⊃ q⦄w) = tt :=
begin
  unfold form_tt_in_wrld, simp, intros, apply a, repeat {assumption}
end

def neg_tt_to_ff {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} (w ∈ 𝓦 ▹ M) {p : form σ} :
  (M⦃~p⦄w) = tt → (M⦃p⦄w) = ff :=
begin
  unfold form_tt_in_wrld, simp,
  intro f, apply eq_ff_of_not_eq_tt,
    apply f, repeat {assumption}, apply M.refl, assumption,
end

def bot_is_insatisf {w : wrld σ} : 
  ¬ ∃ (M : 𝓦 ⸴ 𝓡 ⸴ 𝓿), (M⦃bot σ⦄ w) = tt :=
by intro h; cases h; exact (bool.no_confusion h_h) 


/- implication axioms -/

def pl1_tt {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} (w ∈ 𝓦 ▹ M) {p q : form σ} (h_per : is_persistent M) :
  (M⦃p ⊃ (q ⊃ p)⦄w) = tt :=
begin
  unfold form_tt_in_wrld, simp, intros,
  apply per_in_wrld, assumption, exact a_4, repeat {assumption}
end

def pl2_tt {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} (w ∈ 𝓦 ▹ M) {p q r : form σ} (h_per : is_persistent M) :
  (M⦃(p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r))⦄w) = tt :=
begin
  apply forall_wrlds_to_impl_tt, assumption, intros,
  apply forall_wrlds_to_impl_tt, assumption, intros, --unfold form_tt_in_wrld, simp, intros, --apply per_in_wrld, assumption, assumption, assumption, apply M.trans, repeat {assumption}, apply M.refl 
  apply forall_wrlds_to_impl_tt, assumption, intros,
  apply impl_tt_to_tt_impl_tt, exact H_3, 
    apply impl_tt_to_tt_impl_tt, exact H_3,
    apply per_in_wrld, assumption, exact H_2, assumption, exact a_4,
      apply per_in_wrld, assumption, exact H_1, assumption, exact a_2, assumption, assumption,
        apply impl_tt_to_tt_impl_tt, exact H_3,
        apply per_in_wrld, assumption, exact H_2, repeat {assumption}, --exact a_4, exact a_3, assumption
end

-- 

/- general facts about contexts -/ 

def ctx_tt_iff_mem_tt {Γ : ctx σ} {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} {w : wrld σ} :
  (M⦃Γ⦄w) = tt ↔ (∀ p, p ∈ Γ → (M⦃p⦄w) = tt) :=
begin
  unfold ctx_tt_in_wrld,
  induction (classical.prop_decidable _),
      apply iff.intro,
          simp, intro,
          simp, assumption, simp 
end

def mem_tt_to_ctx_tt (Γ : ctx σ) {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} {w : wrld σ} :
 (∀ (p : form σ) (h : p ∈ Γ), (M⦃p⦄w) = tt) → (M⦃Γ⦄w) = tt :=
ctx_tt_iff_mem_tt.2

def ctx_tt_to_mem_tt {Γ : ctx σ} {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} {w : wrld σ} {p : form σ} :
  (M⦃Γ⦄w) = tt → p ∈ Γ → (M⦃p⦄w) = tt :=
by intro; apply ctx_tt_iff_mem_tt.1; assumption

/- context projections -/

def cons_ctx_tt_iff_and {Γ : ctx σ} {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} {w : wrld σ} {p : form σ} : 
  (M⦃(Γ ⸴ p)⦄w) = tt ↔ (M⦃Γ⦄w) = tt ∧ (M⦃p⦄w) = tt :=
begin
  unfold ctx_tt_in_wrld,
  induction (classical.prop_decidable (∀ p, p ∈ Γ → form_tt_in_wrld M p w = tt)),
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

def cons_ctx_tt_to_ctx_tt {Γ : ctx σ} {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} {w : wrld σ} {p : form σ} : 
  (M⦃(Γ ⸴ p)⦄w) = tt → (M⦃Γ⦄w) = tt :=
by intro h; apply and.elim_left; apply cons_ctx_tt_iff_and.1 h

def ctx_tt_cons_tt_to_cons_ctx_tt {Γ : ctx σ} {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} {w : wrld σ} {p : form σ} : 
  (M⦃Γ⦄w) = tt → (M⦃p⦄w) = tt → (M⦃(Γ ⸴ p)⦄w) = tt :=
by intros hg hp; apply cons_ctx_tt_iff_and.2; split; assumption; assumption

-- persistency

def per_in_ctx {Γ : ctx σ} {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} (v ∈ 𝓦 ▹ M) (w ∈ 𝓦 ▹ M) : 
  (is_persistent M) → (𝓡 ▹ M) w v = tt → ((M⦃Γ⦄w) = tt → (M⦃Γ⦄v) = tt) :=
begin
  intros f rwv hg, apply mem_tt_to_ctx_tt,
    intros p hp, apply per_in_wrld, assumption, exact H, assumption, assumption,
      apply ctx_tt_to_mem_tt hg hp  
end

/- sub-contexts -/

def ctx_tt_to_subctx_tt {Γ Δ : ctx σ} {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} {w : wrld σ} : 
  (M⦃Γ⦄w) = tt → Δ ⊆ Γ → (M⦃Δ⦄w) = tt :=
begin
  intros h s, 
    apply ctx_tt_iff_mem_tt.2, 
      intros p pmem,
         apply ctx_tt_iff_mem_tt.1 h,
           apply s, exact pmem
end

/- the deduction metatheorem -/

def sem_deduction {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⊨ᵢ q) → (Γ ⊨ᵢ p ⊃ q) :=
begin
 intro h,
 induction h,
   apply sem_csq.is_true,
   intros M w h_per ant,
   unfold form_tt_in_wrld, simp,
   intros, apply h, repeat {assumption}, apply ctx_tt_cons_tt_to_cons_ctx_tt,
     apply per_in_ctx, assumption, exact a_1, repeat {assumption}
end
