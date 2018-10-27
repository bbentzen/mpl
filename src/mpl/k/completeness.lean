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
        induction (encodable.decode (form σ) _), simp,
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
              simp,
              simp, induction (prop_decidable _), 
                repeat {simp, apply mem_ext_cons_left}
          },
    intro q,
    unfold ext_ctx_to_max_set_at ext_ctx_with_form,
      induction (encodable.decode (form σ) _), simp,
        induction (encodable.decode (form σ) _), simp,
          simp, induction (prop_decidable _), 
            repeat {simp, apply mem_ext_cons_left},
        simp, induction (prop_decidable _), 
          simp, induction (encodable.decode (form σ) _), simp,
            simp, induction (prop_decidable _), 
              repeat {simp, apply mem_ext_cons_left},
          simp, induction (encodable.decode (form σ) _), simp,
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
  (ext_ctx_to_max_set Γ ⊢ₖ p) → ∃ n, ext_ctx_to_max_set_at Γ n ⊢ₖ p :=
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
              assumption,
    constructor,
      apply prf.k,
      exact 0,
    apply absurd h_cnil,
      apply has_mem_iff_nonempty_ctx.1,
        cases ext_ctx_is_max h_p,
          repeat {constructor, assumption}
end

def max_ext_preserves_consist {Γ : ctx σ} :
  is_consist Γ ⇒ is_consist (ext_ctx_to_max_set Γ) :=
by intros hc nc; cases ext_ctx_lvl nc; apply ctx_consist_ext_ctx_at_consist; repeat {assumption}

/- maximal consistent sets are closed under derivability -/

def max_set_clsd_deriv {Γ : ctx σ} {p : form σ} (hc : is_consist Γ) :
  (ext_ctx_to_max_set Γ ⊢ₖ p) ⇒ p ∈ ext_ctx_to_max_set Γ :=
begin
  intro h,
    cases ext_ctx_is_max p,
      assumption,
      apply false.rec,
        apply max_ext_preserves_consist, assumption,
        apply prf.mp, apply prf.ax, assumption, assumption
end

/- the canonical model construction -/

local attribute [instance] prop_decidable

-- domain

def set_max_wrlds (σ : nat) : set (wrld σ) := image (λ w, ext_ctx_to_max_set w) {w | is_consist w }

def all_wrlds_are_max {w : wrld σ} :
  w ∈ set_max_wrlds σ → ∀ p, (p ∈ w) ∨ ((~p) ∈ w) :=
by intro h; cases h; cases h_h; rewrite (eq.symm h_h_right); apply ext_ctx_is_max

def all_wrlds_are_consist {w : wrld σ} :
  w ∈ set_max_wrlds σ → is_consist w :=
by intro h; cases h; cases h_h; rewrite (eq.symm h_h_right); apply max_ext_preserves_consist; assumption 

def max_cons_set_in_all_wrlds {w : wrld σ} :
  is_consist w → ext_ctx_to_max_set w ∈ set_max_wrlds σ:=
begin
  intro h, constructor, constructor, assumption, reflexivity
end

-- accessibility

def unbox_form_in_wrld (w : wrld σ) : nat → wrld σ :=
λ n, option.rec_on (encodable.decode (form σ) n) · 
  (λ p, form.rec_on p
    (λ v, ·) · (λ q r _ _, ·) 
    (λ q _, if (◻q) ∈ w then {q} else · ) --then set.sep (λ x, x ≠ ◻q) (w ⸴ q) else · )
  )

@[reducible]
def unbox_wrld (w : wrld σ) : wrld σ := 
⋃₀ (image (λ n, unbox_form_in_wrld w n) {n | true})

noncomputable def wrlds_to_access : wrld σ → wrld σ → bool :=
assume w v, if (unbox_wrld w ⊆ v) then tt else ff

-- valuation

noncomputable def wrlds_to_val : var σ → wrld σ → bool :=
assume p w, if w ∈ set_max_wrlds σ ∧ (#p) ∈ w then tt else ff

noncomputable def canonical_model : @model σ :=
begin
  apply model.mk,
    apply set_max_wrlds,
    apply wrlds_to_access,
    apply wrlds_to_val
end

-- unboxing lemmas 

def in_unbox_box_in_wrld {p : form σ} {w : wrld σ} :
  p ∈ unbox_wrld w ↔ (◻p) ∈ w :=
begin
  apply iff.intro, 
    intro h, cases h, cases h_h,
      cases h_h_w, cases h_h_w_h, cases h_h_w_h_right, 
        revert h_h_h, induction (encodable.decode (form σ) _),
          simp, intro, apply false.rec, assumption,
          simp, induction val,
            repeat {simp, intro h, apply false.rec, assumption},
            simp, unfold ite, induction (prop_decidable _),
              simp, intro, apply false.rec, assumption,
              simp, intro h, cases h,
                  rewrite h_1, assumption,
                  apply false.rec, assumption,
    intro h, unfold unbox_wrld image sUnion,
      constructor, constructor, constructor, constructor,
        trivial, reflexivity,
        exact encodable.encode (◻p),
        unfold unbox_form_in_wrld ite,
          rewrite (encodable.encodek ◻p),
            simp, induction p,
            repeat {
              induction prop_decidable _,
                contradiction,
                simp, exact trivial_mem_left
            }        
end

def not_box_in_wrld_not_in_unbox {p : form σ} {w : wrld σ} (hc : w ∈ set_max_wrlds σ) :
  (~◻p) ∈ w → p ∉ unbox_wrld w :=
λ h np, (all_wrlds_are_consist hc) (prf.mp (prf.ax h) (prf.ax (in_unbox_box_in_wrld.1 np)))

def unbox_prvble_box_in_wrld {p : form σ} {w : wrld σ} (hc : w ∈ set_max_wrlds σ) :
  (unbox_wrld w ⊢ₖ p) ⇒ (◻p) ∈ w :=
begin
  cases hc, cases hc_h, rewrite (eq.symm hc_h_right), 
    intro h, induction h,
      apply in_unbox_box_in_wrld.1 h_h,
      repeat {
        apply max_set_clsd_deriv hc_h_left,
          apply prf.full_nec,
            apply prf.pl1 <|> apply prf.pl2 <|> apply prf.pl3,
      },
      apply max_set_clsd_deriv hc_h_left,
        apply prf.mp, apply prf.ax,
          apply max_set_clsd_deriv hc_h_left,
            apply prf.mp,
              apply prf.k, exact h_p,
        repeat {apply prf.ax, assumption},
    apply max_set_clsd_deriv hc_h_left,
      apply prf.full_nec,
        apply prf.k,
    apply max_set_clsd_deriv hc_h_left,
      apply prf.full_nec,
        rewrite (eq.symm h_cnil),
        apply prf.full_nec,
          rewrite (eq.symm h_cnil),
          assumption
end

def not_box_in_wrld_unbox_not_prvble {p : form σ} {w : wrld σ} (hw : w ∈ set_max_wrlds σ) :
  (~◻p) ∈ w → (unbox_wrld w ⊬ₖ p) :=
begin
  intros h nhp,
    apply all_wrlds_are_consist hw,
      apply prf.mp,
        apply prf.ax h,
        apply prf.ax (unbox_prvble_box_in_wrld hw nhp)
end

def not_box_in_wrld_to_consist_not {p : form σ} {w : wrld σ} (hw : w ∈ set_max_wrlds σ) :
  (~◻p) ∈ w → is_consist (unbox_wrld w ⸴ (~p)) :=
λ hn, not_prvb_to_neg_consist (not_box_in_wrld_unbox_not_prvble hw hn)

/- truth is membership in the canonical model -/

def tt_iff_in_wrld {p : form σ} : 
  ∀ (w : wrld σ) (wm : w ∈ set_max_wrlds σ), (canonical_model ⦃p⦄ w) = tt ⇔ p ∈ w :=
begin
  induction p,
    intros, unfold form_tt_in_wrld canonical_model wrlds_to_val, simp,
      apply iff.intro,
        intro h, cases h, assumption,
        intro, split, repeat {assumption},
    
    unfold form_tt_in_wrld, simp,
      intros _ _ h, apply all_wrlds_are_consist wm, apply prf.ax h,

    unfold form_tt_in_wrld, simp, intros, 
      cases wm, cases wm_h, induction wm_h_right,
        apply iff.intro,
          intro h, cases h,
            cases ext_ctx_is_max p_a_1,
                  apply max_set_clsd_deriv, assumption,
              apply prf.mp, apply prf.pl1,
              apply prf.ax, assumption,
            apply max_set_clsd_deriv, assumption,
              apply prf.mp, apply prf.contrap,
                apply prf.mp, apply prf.pl1,
                apply prf.ax, cases ext_ctx_is_max p_a,
                  apply false.rec, apply ff_eq_tt_eq_false,
                    exact (eq.trans (eq.symm h) ((p_ih_a _ (max_cons_set_in_all_wrlds wm_h_left)).2 h_2)),
                  assumption,
          apply max_set_clsd_deriv, assumption,
            apply prf.mp, apply prf.pl1,
              apply prf.ax ((p_ih_a_1 _ (max_cons_set_in_all_wrlds wm_h_left)).1 h), 
        intro h,
          cases ext_ctx_is_max p_a,
            right, apply (p_ih_a_1 _ (max_cons_set_in_all_wrlds wm_h_left)).2,
              apply max_set_clsd_deriv, assumption,
                apply prf.mp, apply prf.ax h, apply prf.ax h_1,
            left, apply eq_ff_of_not_eq_tt, intro p_a_tt,
              apply max_ext_preserves_consist, assumption,
                apply prf.mp,
                  apply prf.ax h_1,
                  apply prf.ax ((p_ih_a _ (max_cons_set_in_all_wrlds wm_h_left)).1 p_a_tt),

    unfold form_tt_in_wrld, simp, intros, 
      apply iff.intro,
        intro h, cases all_wrlds_are_max wm ◻p_a,
          assumption,
          apply false.rec, apply max_ext_preserves_consist,
            apply not_box_in_wrld_to_consist_not wm h_1,
              apply prf.mp,
                apply prf.ax, apply ctx_is_subctx_of_max_ext,
                  exact trivial_mem_left,
                apply prf.ax,
                  apply (p_ih _ (max_cons_set_in_all_wrlds (not_box_in_wrld_to_consist_not wm h_1))).1,
                    apply h,
                      assumption,
                      exact max_cons_set_in_all_wrlds (not_box_in_wrld_to_consist_not wm h_1),
                      unfold canonical_model wrlds_to_access, simp, 
                        intros p pm, apply ctx_is_subctx_of_max_ext, 
                          apply mem_ext_cons_left, assumption,
        intros h v, unfold canonical_model wrlds_to_access,
          simp, intros ww vw rwv,
            apply (p_ih _ vw).2,
              apply rwv, apply in_unbox_box_in_wrld.2,
                assumption
end

def ctx_is_tt (Γ : ctx σ) (wm : Γ ∈ set_max_wrlds σ) : 
  (canonical_model ⦃Γ⦄ Γ) = tt :=
mem_tt_to_ctx_tt Γ (λ p pm, (tt_iff_in_wrld _ wm).2 pm)

/- the completeness theorem -/

def cmpltnss {Γ : ctx σ} {p : form σ} : 
  (Γ ⊨ₖ p) ⇒ (Γ ⊢ₖ p) :=
begin
  apply not_contrap, intros nhp hp, cases hp,
  have c : is_consist (Γ ⸴ ~p) := not_prvb_to_neg_consist nhp,
  apply absurd,
    apply hp,
      apply cons_ctx_tt_to_ctx_tt,
        apply ctx_tt_to_subctx_tt,
          apply ctx_is_tt (ext_ctx_to_max_set (Γ ⸴ ~p)),
            apply max_cons_set_in_all_wrlds c,
            apply ctx_is_subctx_of_max_ext,

      simp, apply neg_tt_iff_ff.1, apply and.elim_right, apply cons_ctx_tt_iff_and.1, 
        apply ctx_tt_to_subctx_tt,
          apply ctx_is_tt (ext_ctx_to_max_set (Γ ⸴ ~p)),
            apply max_cons_set_in_all_wrlds c,
            apply ctx_is_subctx_of_max_ext,
end
