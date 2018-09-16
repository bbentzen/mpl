/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .consistency

open classical

variables {σ : nat}

/- maximal consistent sets -/

inductive is_max (Γ : ctx σ) (p : form σ)
| mem : (p ∈ Γ) → is_max
| nmem : ((~p) ∈ Γ) → is_max

def max_set (Γ : ctx σ) : Type :=
Π p, is_max Γ p

def max_cons_set_clsd_prvb {Γ : ctx σ} {p q : form σ} (m : max_set Γ) (c : is_consist Γ) : 
  p ∈ Γ ⇒ (Γ ⊢ₖ p ⊃ q) ⇒ q ∈ Γ :=
begin
  intros hp hpq,
  cases (m q), assumption,
  apply false.elim,
    apply c,
      apply prf.mp,
        exact (prf.cut hpq (prf.ax a)),
        exact (prf.ax hp)
end

/- from contexts to maximal sets -/

local attribute [instance] prop_decidable

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

def ctx_is_subctx_of_ext_append {Γ : ctx σ} {p : form σ} :
  Γ ⊆ ext_ctx_to_max_set (Γ ⸴ p) :=
begin
  intro hs, unfold ext_ctx_to_max_set, 
  induction (list_form σ), 
    simp, intro, apply or.intro_right, assumption,
    intro hp, simp at *, induction (prop_decidable (is_consist _)), 
      repeat {simp, apply or.intro_right, exact ih hp},
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

/- the canonical model construction -/

-- there exists a set of all maximal consistent sets

axiom all_wrlds (σ : nat) : list (ctx σ)

axiom all_wrlds_max : ∀ (w : ctx σ), w ∈ (@all_wrlds σ) → (max_set w)

axiom all_max_in_wrlds : ∀ (w : ctx σ), (max_set w) → w ∈ (@all_wrlds σ)

axiom all_wrlds_consist : ∀ (w : ctx σ), w ∈ (@all_wrlds σ) → (is_consist w)

def unbox : ctx σ → ctx σ
| · := ·
| (Γ ⸴ p) :=
  begin induction p, exact (unbox Γ), exact (unbox Γ), exact (unbox Γ), exact ((unbox Γ) ⸴ p_a), end

noncomputable def wrlds_to_access (W : list (ctx σ)) : ctx σ → ctx σ → bool :=
assume w v, if (unbox w ⊆ v) then tt else ff

noncomputable def wrlds_to_val (W : list (ctx σ)) : (var σ → ctx σ → bool) :=
assume p w, if ((#p) ∈ w) then tt else ff

noncomputable def canonical_model : (𝓦 ⸴ 𝓡 ⸴ 𝓿) σ :=
begin
  apply model.mk,
    exact (all_wrlds _),
    exact wrlds_to_access (all_wrlds _),
    exact wrlds_to_val (all_wrlds _)
end

-- unboxing lemmas

def exists_wrld_ff_access {p : form σ} {w : ctx σ} {wmem : w ∈ all_wrlds σ} :
  (~◻p) ∈ w ⇒ ∃ v, v ∈ all_wrlds σ ∧ (~p) ∈ v:=
begin
  intro h,
  apply exists.intro,
    split,
    apply all_max_in_wrlds,
      apply ext_ctx_is_max ((unbox w) ⸴ (~p)),
    apply ctx_is_subctx_of_ext,
      apply trivial_mem_left
end

def append_unbox {p q : form σ} {w : ctx σ} :
  (unbox w ⊢ₖ q) ⇒ (unbox (w ⸴ p) ⊢ₖ q) :=
begin
  induction p, repeat {unfold unbox, apply id},
  unfold unbox, intro h, apply prf.weak, assumption
end

def in_unbox_iff_has_box {p : form σ} {w : ctx σ} :
  p ∈ unbox w ⇔ (◻p) ∈ w :=
begin
  apply iff.intro,
  repeat {
    induction w, unfold unbox, simp,
      unfold unbox, simp, induction w_hd,
      repeat {simp, assumption},
      simp, intro h,
        cases h,
          apply or.intro_left,
            assumption,
          apply or.intro_right,
            apply w_ih,
              assumption
  }
end

def in_unbox_prvb {p : form σ} {w : ctx σ} :
  (unbox w ⊢ₖ p) ⇒ (w ⊢ₖ ◻p) :=
begin
  intro h, induction h,
    apply prf.ax,
      apply in_unbox_iff_has_box.1,
        assumption,
    apply prf.full_nec,
      apply prf.pl1,
    apply prf.full_nec,
      apply prf.pl2,
    apply prf.full_nec,
      apply prf.pl3,
    apply prf.mp,
      apply prf.mp,
        apply prf.k,
          exact h_p,
          exact h_ih_hpq,
      assumption,
    apply prf.full_nec,
      apply prf.k,
    apply prf.full_nec,
      apply prf.full_nec,
        induction h_cnil,
          assumption
end

def unbox_prv_in_wrld {p : form σ} {w : ctx σ} {wmem : w ∈ all_wrlds σ} :
  (unbox w ⊢ₖ p) ⇒ (◻p) ∈ w :=
begin
  intro h,
    cases ((all_wrlds_max w wmem) ◻p),
      assumption,
      apply false.rec,
        apply all_wrlds_consist w wmem,
          apply prf.mp,
            exact prf.ax a,
            exact in_unbox_prvb h,
end

def unbox_is_consist {p : form σ} {w : ctx σ} {wmem : w ∈ all_wrlds σ} :
  (~◻p) ∈ w ⇒ is_consist (unbox w ⸴ ~p) :=
begin
  intros h nc,
    apply not_prvb_to_neg_consist,
    cases (em ((◻p) ∈ w)),
      intro, apply all_wrlds_consist w wmem,
          apply prf.mp,
            exact prf.ax h,
            exact prf.ax h_1,
      intro hb, apply h_1,
        apply unbox_prv_in_wrld hb,
        repeat {assumption}
end

def ext_unbox_is_consist {p : form σ} {w : ctx σ}  {wmem : w ∈ all_wrlds σ} :
  (~◻p) ∈ w ⇒ is_consist (ext_ctx_to_max_set (unbox w ⸴ ~p)) :=
begin
  intros h, apply max_ext_preservs_consist,
    apply unbox_is_consist, repeat {assumption}
end

-- canonical model: truth = membership

def tt_iff_in_wrld {p : form σ} : 
  ∀ (w : ctx σ) (wmem : w ∈ all_wrlds σ), (canonical_model ⦃p⦄ w) = tt ⇔ p ∈ w :=
begin
  induction p,
    unfold form_tt_in_wrld,
      unfold canonical_model, simp,
      unfold wrlds_to_val, simp,
    intros, apply iff.intro,
      intro h, apply false.rec,
        apply bot_is_insatisf,
          apply exists.intro,
                assumption,
      intro, apply false.rec,
        apply all_wrlds_consist,
          assumption,
          exact (prf.ax a),

    intros, apply iff.intro,
      unfold form_tt_in_wrld, simp,
      intro h, 
        cases h,
          cases ((all_wrlds_max w wmem) (p_a ⊃ p_a_1)),
            assumption,
            cases ((all_wrlds_max w wmem) p_a),
              apply false.rec,
                exact (bool.no_confusion (eq.trans (eq.symm ((p_ih_a w wmem).2 a_1)) h)),
              apply false.rec,
                apply all_wrlds_consist,
                  assumption,
                apply prf.mp,
                  exact (prf.ax a_1),
                  apply prf.mp, apply (prf.deduction prf.and_elim_left),
                    exact (~p_a_1),
                    apply prf.mp,
                      apply prf.not_impl_to_and_not,
                      exact prf.ax a,
          cases ((all_wrlds_max w wmem) (p_a ⊃ p_a_1)),
            assumption,
            apply false.rec,
              apply all_wrlds_consist,
                assumption,
              apply prf.mp,
                exact prf.ax a, 
                apply prf.mp,
                  exact prf.pl1 _, 
                  apply prf.ax,
                    exact (p_ih_a_1 w wmem).1 h,
      intro h,
        apply not_ff_iff_tt.1,
          unfold form_tt_in_wrld, simp,
          intro h', cases h',
          apply false.rec,
            apply all_wrlds_consist,
              assumption,
            cases ((all_wrlds_max w wmem) p_a_1),
              exact (bool.no_confusion (eq.trans (eq.symm ((p_ih_a_1 w wmem).2 a)) h'_right)),
              apply false.rec,
                apply all_wrlds_consist,
                  assumption,
                apply prf.mp, exact prf.ax a,
                  apply prf.mp,
                    exact prf.ax h,
                      apply prf.ax _,
                      apply (p_ih_a w wmem).1,
                        assumption,

    intros, apply iff.intro,
      unfold form_tt_in_wrld, simp,

      intro h,
        cases ((all_wrlds_max w wmem) ◻p_a),
          assumption,
          have h' : (canonical_model ⦃p_a⦄ (ext_ctx_to_max_set ((unbox w) ⸴ (~p_a))  )) = tt :=
            begin
              apply h,
                exact wmem,
                apply all_max_in_wrlds,
                  apply ext_ctx_is_max,
                unfold canonical_model,
                unfold wrlds_to_access,
                simp, apply ctx_is_subctx_of_ext_append
            end,
          apply false.rec,
            apply ext_unbox_is_consist,
              assumption, assumption,
            apply prf.mp,
              apply prf.ax,
                apply ctx_is_subctx_of_ext,
                  exact trivial_mem_left,
              apply prf.ax,
                apply (p_ih _ _).1,
                  apply h',
            apply all_max_in_wrlds,
              apply ext_ctx_is_max,
      intro h,
        unfold form_tt_in_wrld, simp,
          intros, apply (p_ih _ _).2,
            revert a_2, unfold canonical_model,
            unfold wrlds_to_access, simp,
              intro hs, apply hs,
                apply in_unbox_iff_has_box.2,
                  exact h, exact a_1
end

/- the (weak) completeness theorem -/

def weak_cmpltnss {p : form σ} : 
  (· ⊨ₖ p) ⇒ (· ⊢ₖ p) :=
begin
  apply not_contrap,
  intros nhp hp, cases hp,
    apply absurd,
      apply hp, unfold ctx_tt_in_wrld,
      exact canonical_model,
      exact (ext_ctx_to_max_set {~p}),
      intro htt,
        apply max_ext_preservs_consist,
          exact not_prvb_to_neg_consist nhp,
          apply prf.mp, apply prf.ax,
            apply ctx_is_subctx_of_ext,
              simp,
            apply prf.ax,
          apply (tt_iff_in_wrld _ _).1,
            exact htt,
            apply all_max_in_wrlds,
              apply ext_ctx_is_max,
end

/- the completeness theorem -/

def cmpltnss {Γ : ctx σ} {p : form σ} : 
  (Γ ⊨ₖ p) ⇒ (Γ ⊢ₖ p) :=
begin
  revert p, induction Γ,
    intro, exact weak_cmpltnss,
    intros p hsp,
      apply prf.conv_deduction,
        apply Γ_ih,
        exact sem_deduction hsp
end
