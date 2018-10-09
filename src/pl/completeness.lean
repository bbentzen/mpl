/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .consistency .encodable .misc

open nat set classical

variables {σ : nat}

/- maximal set of a context -/

def ext_ctx_with_form (Γ : ctx σ) : nat → ctx σ :=
λ n, option.rec_on (encodable.decode (form σ) n) Γ (λ p,
  decidable.rec_on (prop_decidable (is_consist (Γ ⸴ p))) (λ hn, Γ ⸴ ~p) (λ h, Γ ⸴ p) )

def ext_ctx_to_max_set_at (Γ : ctx σ) : nat → ctx σ
| 0     := ext_ctx_with_form Γ 0
| (n+1) := ext_ctx_with_form (ext_ctx_to_max_set_at n) (n+1)

@[reducible]
def ext_ctx_to_max_set (Γ : ctx σ) : ctx σ := 
⋃₀ (image (λ n, ext_ctx_to_max_set_at Γ n) {n | true})

/- maximal extensions are extensions -/

def ctx_is_sub_ext_ctx_at {Γ : ctx σ} : 
  ∀ n, Γ ⊆ ext_ctx_to_max_set_at Γ n :=
begin
  intros n v,
    induction n,
      unfold ext_ctx_to_max_set_at ext_ctx_with_form,
        induction (encodable.decode (form σ) _),
         simp, apply id,
         simp, induction (prop_decidable _), 
           repeat {simp, apply mem_ext_cons_left},
      unfold ext_ctx_to_max_set_at ext_ctx_with_form,
        induction (encodable.decode (form σ) _),
         simp, assumption,
         simp, induction (prop_decidable _), 
           repeat {simp, intro, apply mem_ext_cons_left, apply n_ih, assumption},
end

def ext_ctx_form_is_sub_ext_ctx_at {Γ : ctx σ} {n : nat} (hn : n ≥ 1) : 
  ext_ctx_with_form (ext_ctx_to_max_set_at Γ (n-1)) n ⊆ ext_ctx_to_max_set_at Γ n :=
begin
  induction n, unfold ext_ctx_to_max_set_at,
    intros _ _, apply false.rec, exact nat.no_confusion (eq_zero_of_le_zero hn),
    unfold ext_ctx_to_max_set_at, simp, intro, apply id,
end

def exists_ext_ctx_form_is_sub_ext_ctx_at {Γ : ctx σ} : 
  ∀ n, ∃ Δ, ext_ctx_with_form Δ n ⊆ ext_ctx_to_max_set_at Γ n :=
begin
  intro n, induction n,
    unfold ext_ctx_to_max_set_at, simp, 
      constructor, intro p, apply id, 
    unfold ext_ctx_to_max_set_at ext_ctx_with_form,
      induction (encodable.decode (form σ) _), 
        simp, constructor, apply ctx_is_sub_ext_ctx_at,
        simp, induction (prop_decidable _), 
          simp, constructor, induction (prop_decidable _), 
            simp, intro, apply id,
            simp, contradiction,
          simp, constructor, induction (prop_decidable _), 
            simp, contradiction,
            simp, intro, apply id
end

def ext_ctx_at_is_sub_max_set {Γ : ctx σ} : 
  ∀ n, ext_ctx_to_max_set_at Γ n ⊆ ext_ctx_to_max_set Γ :=
begin
  intros n v,
    intro hm, apply exists.intro,
      apply exists.intro,
        apply exists.intro, split,
          exact trivial,
          reflexivity,
        exact n,
      assumption
end

def ext_ctx_at_sub_next {Γ : ctx σ} {n : nat} :
  ext_ctx_to_max_set_at Γ n ⊆ ext_ctx_to_max_set_at Γ (n+1) :=
begin
  induction n,
    intro q,
    unfold ext_ctx_to_max_set_at ext_ctx_with_form,
      simp, induction (encodable.decode (form σ) _), 
        simp, intro, induction (encodable.decode (form σ) _),
          simp, assumption,
          simp, induction (prop_decidable _), 
            repeat {simp, apply mem_ext_cons_left, assumption},
        simp, induction (prop_decidable _), 
          repeat {
            simp, induction (encodable.decode (form σ) _), 
              simp, apply id,
              simp, induction (prop_decidable _), 
                repeat {simp, apply mem_ext_cons_left}
          },
    intro q,
    unfold ext_ctx_to_max_set_at ext_ctx_with_form,
      induction (encodable.decode (form σ) _), simp,
        induction (encodable.decode (form σ) _), simp,
          apply id,
          simp, induction (prop_decidable _), 
            repeat {simp, apply mem_ext_cons_left},
        simp, induction (prop_decidable _), 
          simp, induction (encodable.decode (form σ) _), simp,
            apply id,
            simp, induction (prop_decidable _), 
              repeat {simp, apply mem_ext_cons_left},
          simp, induction (encodable.decode (form σ) _),
            simp, apply id,
            simp, induction (prop_decidable _), 
              repeat {simp, apply mem_ext_cons_left},
end

def ext_ctx_le_to_sub {Γ : ctx σ} {m n : nat} (h : n ≤ m) :
  ext_ctx_to_max_set_at Γ n ⊆ ext_ctx_to_max_set_at Γ m :=
begin
    cases h, intro, apply id,
    cases nat.le.dest h, induction h_1,
      induction w,
    intro, apply id,
    intros q qm,
      apply ext_ctx_at_sub_next,
        apply w_ih,
          apply nat.le_add_right,
          repeat {assumption}
end

def ctx_is_subctx_of_max_ext {Γ : ctx σ} :
  Γ ⊆ ext_ctx_to_max_set Γ :=
begin
  intros _ _, apply ext_ctx_at_is_sub_max_set,
  apply ctx_is_sub_ext_ctx_at, repeat {assumption}
end

/- maximal extensions are maximal -/

def ext_ctx_with_form_of_its_code {Γ : ctx σ} {p : form σ} : 
  (p ∈ ext_ctx_with_form Γ (encodable.encode p)) ∨ ((~p) ∈ ext_ctx_with_form Γ (encodable.encode p)) :=
begin
  unfold ext_ctx_with_form,
  rewrite (encodable.encodek p),
    simp, induction (prop_decidable _), 
      simp, right, apply trivial_mem_left,
      simp, left, apply trivial_mem_left
end

def ext_ctx_is_max {Γ : ctx σ} (p : form σ) : 
  (p ∈ ext_ctx_to_max_set Γ) ∨ ((~p) ∈ ext_ctx_to_max_set Γ) :=
begin
  cases ext_ctx_with_form_of_its_code,
    left,
      apply ext_ctx_at_is_sub_max_set,
        apply ext_ctx_form_is_sub_ext_ctx_at, 
        apply no_code_is_zero p, assumption,
    right,
      apply ext_ctx_at_is_sub_max_set,
        apply ext_ctx_form_is_sub_ext_ctx_at, 
        apply no_code_is_zero p, assumption,
end

/- maximal extensions preserves consistency -/

def ctx_consist_ext_ctx_at_consist {Γ : ctx σ} : 
  ∀ n, is_consist Γ → is_consist (ext_ctx_to_max_set_at Γ n) :=
begin
  intros n hc,
    induction n,
      unfold ext_ctx_to_max_set_at ext_ctx_with_form,
        induction (encodable.decode (form σ) _),
         simp, assumption,
         simp, induction (prop_decidable _), 
           repeat {simp, apply mem_ext_cons_left},
           apply inconsist_to_neg_consist, repeat {assumption},
      unfold ext_ctx_to_max_set_at ext_ctx_with_form,   
        induction (encodable.decode (form σ) _),
         simp, assumption,
         simp, induction (prop_decidable _), 
           simp, apply inconsist_to_neg_consist, repeat {assumption},
end

def in_ext_ctx_max_set_is_in_ext_ctx_at {Γ : ctx σ} {p : form σ} :
  (p ∈ ext_ctx_to_max_set Γ) → ∃ n, p ∈ ext_ctx_to_max_set_at Γ n :=
begin
  intro h, cases h, cases h_h, cases h_h_w, cases h_h_w_h, 
    apply exists.intro, apply eq.substr, exact h_h_w_h_right, assumption
end

def ext_ctx_lvl {Γ : ctx σ} {p : form σ} :
  (ext_ctx_to_max_set Γ ⊢ₚ p) → ∃ n, ext_ctx_to_max_set_at Γ n ⊢ₚ p :=
begin
  intro h, induction h,
    cases in_ext_ctx_max_set_is_in_ext_ctx_at h_h,
      constructor, apply prf.ax, assumption,
    repeat {
      constructor,
      apply prf.pl1 <|> apply prf.pl2 <|> apply prf.pl3,
        exact 0
    },
    cases h_ih_hpq with n0 h_ext_pq, 
      cases h_ih_hp with n1 h_ext_p,
        cases (prop_decidable (n0 ≤ n1)),
            have hh: n1 ≤ n0 :=
              begin
                cases nat.le_total, 
                assumption, 
                contradiction 
            end,
          constructor,
            apply prf.mp,
            assumption,
              apply prf.sub_weak,
                exact h_ext_p,
                apply ext_ctx_le_to_sub,
                assumption,
          constructor,
            apply prf.mp,
              apply prf.sub_weak,
                exact h_ext_pq,
                apply ext_ctx_le_to_sub,
                assumption,
              assumption
end

def max_ext_preserves_consist {Γ : ctx σ} :
  is_consist Γ ⇒ is_consist (ext_ctx_to_max_set Γ) :=
by intros hc nc; cases ext_ctx_lvl nc; apply ctx_consist_ext_ctx_at_consist; repeat {assumption}

/- maximal consistent sets are closed under derivability -/

def max_set_clsd_deriv {Γ : ctx σ} {p : form σ} (hc : is_consist Γ) :
  (ext_ctx_to_max_set Γ ⊢ₚ p) ⇒ p ∈ ext_ctx_to_max_set Γ :=
begin
  intro h,
    cases ext_ctx_is_max p,
      assumption,
      apply false.rec,
        apply max_ext_preserves_consist, assumption,
        apply prf.mp, apply prf.ax, assumption, assumption
end

/- from maximal sets to valuations -/

local attribute [instance] prop_decidable

noncomputable def max_cons_set_val (Γ : ctx σ) : var σ → bool :=
λ v, if #v ∈ (ext_ctx_to_max_set Γ) then tt else ff

def tt_iff_in_max_set {Γ : ctx σ} {p : form σ} (hc : is_consist Γ) : 
  (⦃p⦄ (max_cons_set_val Γ)) = tt ⇔ p ∈ ext_ctx_to_max_set Γ :=
begin
  induction p,
    unfold form_tt_in_val max_cons_set_val, simp,
    unfold form_tt_in_val, simp,
      intro, apply max_ext_preserves_consist hc,
        apply prf.ax, assumption,
    unfold form_tt_in_val, simp at *,
    apply iff.intro,
      intro h, cases h,
        cases ext_ctx_is_max p_a_1,
          apply max_set_clsd_deriv hc,
            apply prf.mp, apply prf.pl1,
            apply prf.ax, assumption,
          apply max_set_clsd_deriv hc,
            apply prf.mp, apply prf.contrap,
              apply prf.mp, apply prf.pl1,
              apply prf.ax, cases ext_ctx_is_max p_a,
                apply false.rec, apply ff_eq_tt_eq_false,
                  exact (eq.trans (eq.symm h) (p_ih_a.2 h_2)),
                assumption,
        apply max_set_clsd_deriv hc,
          apply prf.mp, apply prf.pl1,
            apply prf.ax (p_ih_a_1.1 h), 
    
      intro h,
        cases ext_ctx_is_max p_a,
          right, apply p_ih_a_1.2,
            apply max_set_clsd_deriv hc,
              apply prf.mp, apply prf.ax h, apply prf.ax h_1,
          left, apply eq_ff_of_not_eq_tt, intro p_a_tt,
            apply max_ext_preserves_consist hc,
              apply prf.mp, apply prf.ax h_1, apply prf.ax (p_ih_a.1 p_a_tt)
end

def max_set_is_tt (Γ : ctx σ) (hc : is_consist Γ) : 
 (⦃ext_ctx_to_max_set Γ⦄ (max_cons_set_val Γ)) = tt :=
mem_tt_to_ctx_tt _ (λ p, (tt_iff_in_max_set hc).2)

/- the completeness theorem -/

def cmpltnss {Γ : ctx σ} {p : form σ} : 
  (Γ ⊨ₚ p) ⇒ (Γ ⊢ₚ p) :=
begin
  apply not_contrap, intros nhp hp, cases hp,
  have c : is_consist (Γ ⸴ ~p) := not_prvb_to_neg_consist nhp,
  apply absurd,
    apply hp,
      apply cons_ctx_tt_to_ctx_tt, simp,
        apply ctx_tt_to_subctx_tt,
          apply (max_set_is_tt (Γ ⸴ ~p)) c,
            apply ctx_is_subctx_of_max_ext,

      simp, apply neg_tt_iff_ff.1, apply and.elim_right, apply cons_ctx_tt_iff_and.1, 
        apply ctx_tt_to_subctx_tt,
          apply (max_set_is_tt (Γ ⸴ ~p)) c,
          apply ctx_is_subctx_of_max_ext,
end