/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .consistency .misc

open nat classical

variables {σ : nat}

/- maximal consistent sets -/

inductive is_max (Γ : ctx σ) (p : form σ)
| mem : (p ∈ Γ) → is_max
| nmem : ((~p) ∈ Γ) → is_max

def max_set (Γ : ctx σ) : Type :=
Π p, is_max Γ p

def max_cons_set_clsd_prvb {Γ : ctx σ} {p q : form σ} (m : max_set Γ) (c : is_consist Γ) : 
  p ∈ Γ ⇒ (Γ ⊢ₚ p ⊃ q) ⇒ q ∈ Γ :=
begin
  intros hp hpq,
  cases (m q), assumption,
  apply false.elim,
    apply c,
      apply prf.mp,
        exact (prf.cut hpq (prf.ax a)),
        exact (prf.ax hp)
end

def is_max_union_left {Γ Δ : ctx σ} {p : form σ} :
is_max Γ p →  is_max (Γ ⊔ Δ) p :=
begin
  intro h, cases h,
  apply is_max.mem,
    exact mem_ext_append_left h,
  apply is_max.nmem,
    exact mem_ext_append_left h,
end

def is_max_union_right {Γ Δ : ctx σ} {p : form σ} :
is_max Δ p →  is_max (Γ ⊔ Δ) p :=
begin
  intro h, cases h,
  apply is_max.mem,
    exact mem_ext_append_right h,
  apply is_max.nmem,
    exact mem_ext_append_right h,
end

/- from maximal sets to valuations -/

def max_cons_set_val {Γ : ctx σ} :
  max_set Γ ⇒ is_consist Γ ⇒ (var σ → bool) :=
λ m c v, is_max.rec_on (m (#v)) (λ hm, tt) (λ hn, ff)

def tt_iff_in_max_set {Γ : ctx σ} {p : form σ} {m : max_set Γ} {c : is_consist Γ} : 
  (⦃p⦄ (max_cons_set_val m c)) = tt ⇔ p ∈ Γ :=
begin
  simp at *,
    induction p,
      unfold true_in_val, unfold max_cons_set_val, 
        induction (m (#p)),
          apply iff.intro, intro, assumption, intro, simp,
          apply iff.intro, contradiction, intro, simp,

      apply c, apply prf.mp,
        exact (prf.ax a),
        exact (prf.ax a_1),
      apply iff.intro, intro,
        apply false.elim,
          apply bot_is_insatisf,
            existsi (max_cons_set_val m c), assumption,
        intro h, apply false.elim, apply c, apply prf.ax h,

      apply iff.intro, intro h,
        cases (impl_tt_iff_ff_or_tt.1 h), simp at *,
          cases (m p_a),
            cases (m p_a_1),
              apply (max_cons_set_clsd_prvb m c),
                exact a_1,
                apply prf.pl1,
              apply absurd a,
                apply contrap p_ih_a.2, simp, exact h_1,
            cases (m (p_a ⊃ p_a_1)),
              assumption,
              apply false.elim, apply c,
                apply prf.mp (prf.ax a),
                  apply prf.ax, apply (max_cons_set_clsd_prvb m c),
                    exact a_1, 
                    apply prf.cut, apply prf.nimpl_to_and,
                      apply prf.deduction, apply prf.and_elim_left,
          simp at *, apply (max_cons_set_clsd_prvb m c),
            exact (p_ih_a_1.1 h_1),
            apply prf.pl1,

      intro h, apply impl_tt_iff_ff_or_tt.2,
      cases (m p_a_1),
        apply or.intro_right,
          exact (p_ih_a_1.2 a),
        apply or.intro_left,
        have nih : p_a ∉ Γ ⇒ true_in_val _ (max_cons_set_val m c) p_a ≠ tt := (contrap p_ih_a.1),
        simp at *, apply nih, intro ha, apply c,
        apply prf.mp (prf.ax a),
          apply prf.mp,
            exact (prf.ax h),
            exact (prf.ax ha)
end

def max_set_is_tt (Γ : ctx σ) {m : max_set Γ} {c : is_consist Γ} :
 (⦃Γ⦄ (max_cons_set_val m c)) = tt :=
mem_tt_to_ctx_tt Γ (λ p, tt_iff_in_max_set.2)

/- from maximal sets to valuations -/

local attribute [instance] prop_decidable

-- TODO: give an explicit construction of the list

axiom list_form (σ : nat) : list (form σ)

axiom has_all_form : ∀ (p : form σ), p ∈ (@list_form σ)

axiom or_to_sum {p q : Prop} : p ∨ q → psum p q

noncomputable def ext_ctx_to_max_set (Γ : ctx σ) : ctx σ :=
list.rec_on (list_form σ) Γ (λ hd tl IH, 
  decidable.rec_on (prop_decidable (is_consist (IH ⸴ hd)))
  (λ (h : ¬is_consist (IH ⸴ hd)), IH ⸴ hd ⊃ ⊥)
  (λ (h : is_consist (IH ⸴ hd)),  IH ⸴ hd) )

/- maximal extensions are maximal, supersets and equiconsistents -/

noncomputable def ext_ctx_is_max (Γ : ctx σ) :
  max_set (ext_ctx_to_max_set Γ) :=
begin
  intro p, 
  unfold ext_ctx_to_max_set, 
  have hp : p ∈ list_form σ := has_all_form p, revert hp,
  induction (list_form σ), 
    intros hp,
      apply false.elim,
      exact ((list.not_mem_nil p) hp),
    intros hp, simp at *,
      cases (or_to_sum hp), induction val,
      induction (prop_decidable (is_consist (_ ⸴ p))), simp,
        apply is_max.nmem, exact trivial_mem_left, simp,
        apply is_max.mem, exact trivial_mem_left, 
      induction (prop_decidable (is_consist (_ ⸴ hd))),
       repeat {
         simp, cases (ih val),
         apply is_max.mem, apply mem_ext_cons_left a,
         apply is_max.nmem, apply mem_ext_cons_left a
       }               
end

def ctx_is_subctx_of_ext {Γ : ctx σ} :
  Γ ⊆ ext_ctx_to_max_set Γ :=
begin
  intro p, unfold ext_ctx_to_max_set, 
  induction (list_form σ), 
    simp, intro, assumption, simp,
    intro hp, induction (prop_decidable (is_consist _)), 
      repeat {
        simp, apply or.intro_right, exact ih hp,
      }
end

def max_ext_preservs_consist {Γ : ctx σ} :
   is_consist Γ ⇒  is_consist (ext_ctx_to_max_set Γ) :=
begin
  intro c, unfold ext_ctx_to_max_set,
  induction (list_form σ),
    simp, assumption, simp,
    induction (prop_decidable (is_consist _ )), simp,
      apply inconsist_to_neg_consist ih h,
      simp, assumption
end

def ni_ext_to_neg_in_ext {Γ : ctx σ} {p : form σ} (c : is_consist Γ) :
   p ∉ (ext_ctx_to_max_set Γ) ⇔ (~p) ∈ (ext_ctx_to_max_set Γ) :=
begin
  apply iff.intro,
    intro nmemp, cases (ext_ctx_is_max Γ p),
      apply false.elim (nmemp a), assumption,
    intros memnp nmemp, apply max_ext_preservs_consist c,
      exact prf.mp (prf.ax memnp) (prf.ax nmemp)
end

def neg_ni_ext_to_in_ext {Γ : ctx σ} {p : form σ} (c : is_consist Γ) :
   (~p) ∉ (ext_ctx_to_max_set Γ) ⇔ p ∈ (ext_ctx_to_max_set Γ) :=
begin
  apply iff.intro,
    intro, cases (ext_ctx_is_max Γ p),
      assumption,
      contradiction,
    intros memp memnp,  apply max_ext_preservs_consist c,
      exact prf.mp (prf.ax memnp) (prf.ax memp)
end

/- the completeness theorem -/

def cmpltnss {Γ : ctx σ} {p : form σ} : 
  (Γ ⊨ₚ p) ⇒ (Γ ⊢ₚ p) :=
begin
  apply em_contrap, intros nhp hp, cases hp,
  have c : is_consist (Γ ⸴ ~p) := not_prvb_to_neg_consist nhp,
  apply absurd,
    apply hp,
      apply cons_ctx_tt_to_ctx_tt, simp,
        apply ctx_tt_to_subctx_tt,
          apply (max_set_is_tt (ext_ctx_to_max_set (Γ ⸴ ~p))),
            apply ext_ctx_is_max,
              exact max_ext_preservs_consist c,
              exact ctx_is_subctx_of_ext,

      simp, apply neg_tt_iff_ff.1, apply and.elim_right, apply cons_ctx_tt_iff_and.1, 
        apply ctx_tt_to_subctx_tt,
        apply (max_set_is_tt (ext_ctx_to_max_set (Γ ⸴ ~p))),
        exact ctx_is_subctx_of_ext
end

