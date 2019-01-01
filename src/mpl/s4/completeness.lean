/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .consistency .misc ..encoding

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
    unfold ext_ctx_to_max_set_at, simp
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
            simp, intro,
            simp, contradiction,
          simp, constructor, induction (prop_decidable _), 
            simp, contradiction, simp
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
        simp, simp, induction (prop_decidable _), 
          repeat {
            simp, induction (prop_decidable _),
              repeat {
                simp, apply mem_ext_cons_left
              },
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
  (ext_ctx_to_max_set Γ ⊢ₛ₄ p) → ∃ n, ext_ctx_to_max_set_at Γ n ⊢ₛ₄ p :=
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
    constructor,
      apply prf.t,
      exact 0,
    constructor,
      apply prf.s4,
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
  (ext_ctx_to_max_set Γ ⊢ₛ₄ p) ⇒ p ∈ ext_ctx_to_max_set Γ :=
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

def set_max_wrlds (σ : nat) : set (wrld σ) := image (λ w, ext_ctx_to_max_set w) {w | is_consist w}

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

def max_wrld_clsd_deriv {Γ : ctx σ} {p : form σ} (Γ ∈ set_max_wrlds σ) :
  (Γ ⊢ₛ₄ p) ⇒ p ∈ Γ :=
begin
  intro h,
    cases all_wrlds_are_max H p,
      assumption,
      apply false.rec,
        cases H, cases H_h, rw eq.symm H_h_right at *,
        apply max_ext_preserves_consist, assumption,
        apply prf.mp, apply prf.ax,
          repeat {assumption}, 
end

-- accessibility

def unbox_form_in_wrld (w : wrld σ) : nat → wrld σ :=
λ n, option.rec_on (encodable.decode (form σ) n) · 
  (λ p, form.rec_on p
    (λ v, ·) · (λ q r _ _, ·) 
    (λ q _, if (◻q) ∈ w then {q} else · )
  )

def unbox_wrld (w : wrld σ) : wrld σ := 
⋃₀ (image (λ n, unbox_form_in_wrld w n) {n | true})

noncomputable def wrlds_to_access : wrld σ → wrld σ → bool :=
assume w v, if (unbox_wrld w ⊆ v) then tt else ff

def in_unbox_box_in_wrld {p : form σ} {w : wrld σ} :
  p ∈ unbox_wrld w ↔ (◻p) ∈ w :=
begin
  apply iff.intro, 
    intro h, cases h, cases h_h,
      cases h_h_w, cases h_h_w_h, cases h_h_w_h_right, 
        revert h_h_h, induction (encodable.decode (form σ) _),
          simp, induction val,
            repeat {simp}, 
            unfold ite, induction (prop_decidable _),
              simp, simp, intro h, cases h, assumption,
    intro h, unfold unbox_wrld image sUnion,
      constructor, constructor, constructor, constructor,
        trivial, reflexivity,
        exact encodable.encode (◻p),
        unfold unbox_form_in_wrld ite,
          rw (encodable.encodek ◻p),
            simp, induction p,
            repeat {
              induction prop_decidable _,
                contradiction, simp,
            }
end

-- valuation

noncomputable def wrlds_to_val : var σ → wrld σ → bool :=
assume p w, if w ∈ set_max_wrlds σ ∧ (#p) ∈ w then tt else ff

-- reflexivity

def all_wrlds_are_refl {w : wrld σ} :
  w ∈ set_max_wrlds σ → wrlds_to_access w w = tt :=
begin
  intro h, unfold wrlds_to_access,
  simp, intros p hp, cases all_wrlds_are_max h p, assumption,
    apply false.rec, apply all_wrlds_are_consist h,
      apply prf.mp, apply prf.ax h_1, 
        apply prf.mp, apply prf.t,
          apply prf.ax, apply in_unbox_box_in_wrld.1, assumption
end

-- transitivity

def all_wrlds_are_trans {w v u : wrld σ} :
  w ∈ set_max_wrlds σ → v ∈ set_max_wrlds σ → u ∈ set_max_wrlds σ → wrlds_to_access w v = tt → wrlds_to_access v u = tt → wrlds_to_access w u = tt:=
begin
  intros hw hv hu, unfold wrlds_to_access,
  simp, intros sw sv p hp,
  apply sv, apply in_unbox_box_in_wrld.2,
    apply sw, apply in_unbox_box_in_wrld.2,
      apply max_wrld_clsd_deriv, assumption, assumption,
      apply prf.mp, apply prf.s4, apply prf.ax,
        apply in_unbox_box_in_wrld.1, assumption
end

-- canonical model

noncomputable def canonical_model : @model σ :=
begin
  fapply model.mk,
    apply set_max_wrlds,
    apply wrlds_to_access,
    apply wrlds_to_val,
    apply all_wrlds_are_refl,
    apply all_wrlds_are_trans
end

-- unboxing lemmas 

def not_box_in_wrld_not_in_unbox {p : form σ} {w : wrld σ} (hc : w ∈ set_max_wrlds σ) :
  (~◻p) ∈ w → p ∉ unbox_wrld w :=
λ h np, (all_wrlds_are_consist hc) (prf.mp (prf.ax h) (prf.ax (in_unbox_box_in_wrld.1 np)))

def unbox_prvble_box_in_wrld {p : form σ} {w : wrld σ} (hc : w ∈ set_max_wrlds σ) :
  (unbox_wrld w ⊢ₛ₄ p) ⇒ (◻p) ∈ w :=
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
    apply max_set_clsd_deriv hc_h_left, -- k
      apply prf.full_nec,
        apply prf.k,
    apply max_set_clsd_deriv hc_h_left, -- t
      apply prf.full_nec,
        apply prf.t,
    apply max_set_clsd_deriv hc_h_left, -- s4
      apply prf.full_nec,
        apply prf.s4,
    apply max_set_clsd_deriv hc_h_left, -- nec
      apply prf.full_nec,
        rewrite (eq.symm h_cnil),
        apply prf.full_nec,
          rewrite (eq.symm h_cnil),
          assumption
end

def not_box_in_wrld_unbox_not_prvble {p : form σ} {w : wrld σ} (hw : w ∈ set_max_wrlds σ) :
  (~◻p) ∈ w → (unbox_wrld w ⊬ₛ₄ p) :=
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
        apply iff.intro,
          intro h, cases h,
            apply max_wrld_clsd_deriv w wm,
              apply prf.mp, apply prf.pl1,
              apply prf.ax, apply (p_ih_a_1 w wm).1 h, assumption, 
            cases all_wrlds_are_max wm p_a,
              apply false.rec, exact bool.no_confusion (eq.trans (eq.symm ((p_ih_a w wm).2 h_1)) h),
              apply max_wrld_clsd_deriv w wm,
                apply prf.mp,
                  exact prf.ex_falso_and,
                  exact prf.ax h_1, assumption,

          intro h,
            cases all_wrlds_are_max wm p_a_1,
              left, exact ((p_ih_a_1 _ wm).2 h_1),
              cases all_wrlds_are_max wm p_a,
                apply false.rec, apply all_wrlds_are_consist wm,
                  apply prf.mp, apply prf.ax h_1,
                    apply prf.mp, apply prf.ax h,
                      apply prf.ax h_2,
                right, apply eq_ff_of_not_eq_tt, intro p_a_tt,
                  apply all_wrlds_are_consist wm,
                    apply prf.mp, apply prf.ax h_2,
                    apply prf.ax ((p_ih_a w wm).1 p_a_tt),

    unfold form_tt_in_wrld, simp, intros, 
      apply iff.intro,
        intro h, 
        cases all_wrlds_are_max wm ◻p_a,
          assumption,
          apply false.rec, 
            apply all_wrlds_are_consist,
              apply max_cons_set_in_all_wrlds,
                apply not_box_in_wrld_to_consist_not wm,
                  assumption,
                  apply prf.mp, apply prf.ax,
                    apply ctx_is_subctx_of_max_ext,
                      apply trivial_mem_left,
                    apply prf.ax,
                      apply (p_ih _ (max_cons_set_in_all_wrlds (not_box_in_wrld_to_consist_not wm h_1))).1,
                      apply h,
                        assumption, 
                        apply max_cons_set_in_all_wrlds (not_box_in_wrld_to_consist_not wm h_1),
                        unfold canonical_model wrlds_to_access, simp,
                          intros q hq, apply ctx_is_subctx_of_max_ext,
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
  (Γ ⊨ₛ₄ p) ⇒ (Γ ⊢ₛ₄ p) :=
begin
  apply not_contrap, intros nhp hp, cases hp,
  have c : is_consist (Γ ⸴ ~p) := not_prvb_to_neg_consist nhp,
  apply absurd,
    fapply hp,
      exact canonical_model,
      exact ext_ctx_to_max_set (Γ ⸴ ~p),
      apply max_cons_set_in_all_wrlds, assumption, 

      apply cons_ctx_tt_to_ctx_tt,
        apply ctx_tt_to_subctx_tt,
          apply ctx_is_tt (ext_ctx_to_max_set (Γ ⸴ ~p)),
            apply max_cons_set_in_all_wrlds c,
            apply ctx_is_subctx_of_max_ext,

      simp, apply neg_tt_iff_ff.1, apply and.elim_right, apply cons_ctx_tt_iff_and.1, 
        apply ctx_tt_to_subctx_tt,
          apply ctx_is_tt (ext_ctx_to_max_set (Γ ⸴ ~p)),
            apply max_cons_set_in_all_wrlds c,
            apply ctx_is_subctx_of_max_ext
end
