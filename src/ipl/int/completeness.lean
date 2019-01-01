/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .consistency ..encoding ..misc

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
  (ext_ctx_to_max_set Γ ⊢ᵢ p) → ∃ n, ext_ctx_to_max_set_at Γ n ⊢ᵢ p :=
begin
  intro h, induction h,
    cases in_ext_ctx_max_set_is_in_ext_ctx_at h_h,
      constructor, apply prf.ax, assumption,
    repeat {
      constructor,
      apply prf.pl1 <|> apply prf.pl2 <|> 
      apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
      apply prf.orr <|> apply prf.orl <|> apply prf.ore <|>
      apply prf.falso, 
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
  (ext_ctx_to_max_set Γ ⊢ᵢ p) ⇒ p ∈ ext_ctx_to_max_set Γ :=
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

def max_wrld_clsd_deriv (w ∈ set_max_wrlds σ) {p : form σ} :
  (w ⊢ᵢ p) ⇒ p ∈ w :=
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

def atompl_form_of (w : wrld σ) : nat → wrld σ :=
λ n, option.rec_on (encodable.decode (form σ) n) · 
  (λ p, form.rec_on p
    (λ v, if (#v) ∈ w then {#v} else · ) 
    · (λ q r _ _, ·) (λ q r _ _, ·) 
    (λ q r _ _, if (q ⊃ r) ∈ w then {q ⊃ r} else · ) 
  )

def atompl_of (w : wrld σ) : wrld σ := 
⋃₀ (image (λ n, atompl_form_of w n) {n | true})

noncomputable def wrlds_to_access : wrld σ → wrld σ → bool :=
assume w v, if (atompl_of w ⊆ v) then tt else ff

def atom_in_atompl (w ∈ set_max_wrlds σ) {p : var σ} : 
  #p ∈ w → #p ∈ atompl_of w :=
begin
  intro, unfold atompl_of atompl_form_of image sUnion, simp,
  fapply exists.intro {#p}, split, 
    fapply exists.intro (encodable.encode (#p)),
      rw (encodable.encodek (#p)), simp, unfold ite,
      induction (prop_decidable _),
        contradiction, simp, constructor, reflexivity,
end

def impl_in_atompl (w ∈ set_max_wrlds σ) {p q : form σ} : 
  p ⊃ q ∈ w → p ⊃ q ∈ atompl_of w :=
begin
  intro, unfold atompl_of atompl_form_of image sUnion, simp,
  fapply exists.intro {p ⊃ q}, split, 
    fapply exists.intro (encodable.encode (p ⊃ q)),
      rw (encodable.encodek (p ⊃ q)), simp, unfold ite,
      induction (prop_decidable _),
        contradiction, simp, constructor, reflexivity,
end

def per_wrlds (w ∈ set_max_wrlds σ) {v : wrld σ} {H_1 : v ∈ set_max_wrlds σ} : 
  Π {p : form σ}, atompl_of w ⊆ v → p ∈ w → p ∈ v
|  (#p)   := begin intros, apply a, apply atom_in_atompl, repeat {assumption} end
| (form.bot _) := begin intros _ h; apply false.rec; apply all_wrlds_are_consist H, apply prf.ax h end
| (p ⊃ q) := begin intros, apply a, apply impl_in_atompl, repeat {assumption} end
| (p & q) :=  begin 
                intros _ h, apply max_wrld_clsd_deriv _ H_1,
                  apply prf.mp, apply prf.mp, apply prf.andi, 
                    repeat {
                      apply prf.ax, apply per_wrlds, repeat {assumption}, apply max_wrld_clsd_deriv _ H,
                      {apply prf.mp, apply prf.andr, exact q, apply prf.ax h} <|> {apply prf.mp, apply prf.andl, exact p, apply prf.ax h}
                    },
              end
| (p ∨ q) :=  begin
                intros _ h,
                cases all_wrlds_are_max H p,
                  repeat{
                    apply max_wrld_clsd_deriv _ H_1, apply prf.mp, 
                    {apply prf.orr} <|> apply prf.orl, apply prf.ax (per_wrlds a h_1)
                  },
                  cases all_wrlds_are_max H q,
                    repeat{
                      apply max_wrld_clsd_deriv _ H_1, apply prf.mp, 
                      {apply prf.orl} <|> apply prf.orr, apply prf.ax (per_wrlds a h_2)
                  },
                    apply false.rec, apply all_wrlds_are_consist H,
                    apply prf.mp, apply prf.mp,
                      apply and_not_not_to_not_or,
                        exact p,
                        exact q,
                        apply prf.mp, apply prf.mp, apply prf.andi,
                          repeat {
                            apply prf.ax,
                            assumption
                          },
              end

def atompl_to_sub (w ∈ set_max_wrlds σ) {v : wrld σ} {H_1 : v ∈ set_max_wrlds σ} :
  atompl_of w ⊆ v → w ⊆ v :=
begin
  intros h p, apply per_wrlds, repeat {assumption}
end

-- reflexivity

def atompl_is_sub_wrld (w ∈ set_max_wrlds σ) :
  atompl_of w ⊆ w :=
begin
  intros p h, cases h, cases h_h, cases h_h_w, cases h_h_w_h, cases h_h_w_h_right,
  revert h_h_w_h_right h_h_h,
  induction (encodable.decode (form σ) _),
    simp, simp,
    induction val,
      simp, unfold ite, induction (prop_decidable _),
        simp, simp, intros, rw h_h_h, assumption,
      repeat {simp},
      unfold ite, induction (prop_decidable _),
        simp, simp, intros, rw h_h_h, assumption
end

def all_wrlds_are_refl {w : wrld σ} :
  w ∈ set_max_wrlds σ → wrlds_to_access w w = tt :=
begin
  intro h, unfold wrlds_to_access, simp,
  apply atompl_is_sub_wrld, exact h 
end

def access_iff_atompl {w v : wrld σ} :
 wrlds_to_access w v = tt ↔ atompl_of w ⊆ v :=
begin
  unfold wrlds_to_access, simp,
end

-- transitivity

def all_wrlds_are_trans {w v u : wrld σ} :
  w ∈ set_max_wrlds σ → v ∈ set_max_wrlds σ → u ∈ set_max_wrlds σ → wrlds_to_access w v = tt → wrlds_to_access v u = tt → wrlds_to_access w u = tt :=
begin
  intro h, unfold wrlds_to_access, simp,
  intros, intros p h,
  have h1 : v ⊆ u := begin apply atompl_to_sub, repeat {assumption} end,
  have h2 : w ⊆ v := begin apply atompl_to_sub, repeat {assumption} end, 
    apply h1, apply h2, apply atompl_is_sub_wrld, repeat {assumption}
end

-- valuation

noncomputable def wrlds_to_val : var σ → wrld σ → bool :=
assume p w, if w ∈ set_max_wrlds σ ∧ (#p) ∈ w then tt else ff

noncomputable def canonical_model : @model σ :=
begin
  fapply model.mk,
    apply set_max_wrlds,
    apply wrlds_to_access,
    apply wrlds_to_val,
    apply all_wrlds_are_refl,
    intros, apply all_wrlds_are_trans, assumption, exact H_1, repeat {assumption}
end

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

    unfold form_tt_in_wrld, simp, intros, -- and
      cases wm, cases wm_h, induction wm_h_right,
        apply iff.intro,
          intro h, cases h,
            apply max_set_clsd_deriv, assumption,
            apply prf.mp, apply prf.mp, apply prf.andi,
              apply prf.ax,
                apply (p_ih_a _ (max_cons_set_in_all_wrlds wm_h_left)).1 h_left,
              apply prf.ax,
                apply (p_ih_a_1 _ (max_cons_set_in_all_wrlds wm_h_left)).1 h_right,
          intro h, split,
            apply (p_ih_a _ (max_cons_set_in_all_wrlds wm_h_left)).2,
              cases ext_ctx_is_max p_a,
                assumption,
                apply false.rec, apply max_ext_preserves_consist, assumption,
                apply prf.mp, apply prf.ax h_1,
                  apply prf.mp, apply prf.andr, exact p_a_1,
                  apply prf.ax, assumption,
            apply (p_ih_a_1 _ (max_cons_set_in_all_wrlds wm_h_left)).2,
              cases ext_ctx_is_max p_a_1,
                assumption,
                apply false.rec, apply max_ext_preserves_consist, assumption,
                apply prf.mp, apply prf.ax h_1,
                  apply prf.mp, apply prf.andl, exact p_a,
                  apply prf.ax, assumption,
    
    unfold form_tt_in_wrld, simp, intros, -- or
      cases wm, cases wm_h, induction wm_h_right,
        apply iff.intro,
          intro h, cases h, 
            apply max_set_clsd_deriv, assumption,
            apply prf.mp, apply prf.orr,
              apply prf.ax,
              apply (p_ih_a _ (max_cons_set_in_all_wrlds wm_h_left)).1 h,
            apply max_set_clsd_deriv, assumption,
            apply prf.mp, apply prf.orl,
              apply prf.ax,
              apply (p_ih_a_1 _ (max_cons_set_in_all_wrlds wm_h_left)).1 h,
          intro h, 
            cases ext_ctx_is_max p_a,
              left, apply (p_ih_a _ (max_cons_set_in_all_wrlds wm_h_left)).2 h_1,
              cases ext_ctx_is_max p_a_1,
                right, apply (p_ih_a_1 _ (max_cons_set_in_all_wrlds wm_h_left)).2 h_2,
                apply false.rec, apply max_ext_preserves_consist, assumption,
                apply prf.mp, apply prf.mp, apply and_not_not_to_not_or, exact p_a, exact p_a_1,
                  apply prf.mp, apply prf.mp, apply prf.andi,
                    repeat {apply prf.ax, assumption},

    unfold form_tt_in_wrld, simp, intros, -- impl
      cases wm, cases wm_h, induction wm_h_right,
        apply iff.intro,
          intros, cases ext_ctx_is_max p_a_1,
            apply max_set_clsd_deriv, assumption,
            apply prf.mp, apply prf.pl1, apply prf.ax, assumption,
            cases ext_ctx_is_max p_a,
              apply false.rec, apply max_ext_preserves_consist, assumption,
                apply prf.mp, apply prf.ax h,
                apply prf.ax,
                    apply (p_ih_a_1 _ (max_cons_set_in_all_wrlds wm_h_left)).1,
                    apply a, repeat {apply max_cons_set_in_all_wrlds, assumption},
                      unfold canonical_model, unfold wrlds_to_access ite, simp,
                      induction (prop_decidable _),
                        simp, apply h_2, apply atompl_is_sub_wrld,
                          apply max_cons_set_in_all_wrlds, assumption, 
                        simp, apply (p_ih_a _ (max_cons_set_in_all_wrlds wm_h_left)).2,
              assumption,
              apply max_set_clsd_deriv, assumption,
                apply prf.mp, apply prf.mp, apply prf.impl_falso,
                  repeat {apply prf.ax, assumption},
            intros,
                apply (p_ih_a_1 _ a_2).2,
                apply max_wrld_clsd_deriv, assumption,
                  apply prf.mp, apply prf.ax,
                    apply access_iff_atompl.1 a_3,
                    apply impl_in_atompl, 
                      apply max_cons_set_in_all_wrlds, assumption,
                      assumption,
                      apply prf.ax, exact (p_ih_a _ a_2).1 a_4, 
end

def ctx_is_tt (Γ : ctx σ) (wm : Γ ∈ set_max_wrlds σ) : 
  (canonical_model ⦃Γ⦄ Γ) = tt :=
mem_tt_to_ctx_tt Γ (λ p pm, (tt_iff_in_wrld _ wm).2 pm)

-- persistency 

def canonical_model_is_persist : is_persistent (@canonical_model σ) :=
begin
  intros p w hw v hv rwv h,
  apply (tt_iff_in_wrld _ hv).2,
  apply atompl_to_sub, apply hw, assumption, exact access_iff_atompl.1 rwv,
    apply (tt_iff_in_wrld _ hw).1, assumption
end

-- useful lemmas

def ff_to_neg_tt {w : wrld σ} {p : form σ} :
  (canonical_model⦃p⦄w) = ff → (canonical_model⦃~p⦄w) = tt :=
begin
  unfold form_tt_in_wrld, simp,
  intros,
  apply false.rec, apply all_wrlds_are_consist a_2,
    apply prf.mp, apply prf.ax,
    cases all_wrlds_are_max a_1 p,
      apply false.rec,
      have htt : (canonical_model⦃p⦄w) = tt := begin apply (tt_iff_in_wrld _ a_1).2 h end,
      rw a at htt, contradiction,
      apply access_iff_atompl.1 a_3,
      apply impl_in_atompl, assumption, assumption,
    apply prf.ax, apply (tt_iff_in_wrld _ a_2).1, assumption
end

def canonical_model_ff_iff_neg_tt (w ∈ set_max_wrlds σ) {p : form σ} :
  (canonical_model⦃p⦄w) = ff ↔ (canonical_model⦃~p⦄w) = tt :=
begin
  unfold form_tt_in_wrld, simp,
  apply iff.intro,
  intros,
  apply false.rec, apply all_wrlds_are_consist a_2,
    apply prf.mp, apply prf.ax,
    cases all_wrlds_are_max a_1 p,
      apply false.rec,
      have htt : (canonical_model⦃p⦄w) = tt := begin apply (tt_iff_in_wrld _ a_1).2 h end,
      rw a at htt, contradiction,
      apply access_iff_atompl.1 a_3,
      apply impl_in_atompl, assumption, assumption,
    apply prf.ax, apply (tt_iff_in_wrld _ a_2).1, assumption,
  intros, apply eq_ff_of_not_eq_tt,
  apply a, assumption, assumption, exact access_iff_atompl.2 (atompl_is_sub_wrld w H)
end

/- the completeness theorem -/

def cmpltnss {Γ : ctx σ} {p : form σ} : 
  (Γ ⊨ᵢ p) ⇒ (Γ ⊢ᵢ p) :=
begin
  apply not_contrap, intros nhp hp, cases hp,
  cases (prop_decidable (Γ ⊢ᵢ ~~p)),
    have c : is_consist (Γ ⸴ ~p) := not_prvb_to_neg_consist h,
    apply absurd,
    fapply hp, 
      exact canonical_model,
      exact (ext_ctx_to_max_set (Γ ⸴ ~p)),
      apply max_cons_set_in_all_wrlds c, 
      apply canonical_model_is_persist,
      apply cons_ctx_tt_to_ctx_tt,
        apply ctx_tt_to_subctx_tt,
          apply ctx_is_tt (ext_ctx_to_max_set (Γ ⸴ ~p)),
            apply max_cons_set_in_all_wrlds c,
            apply ctx_is_subctx_of_max_ext,

      simp, apply (canonical_model_ff_iff_neg_tt _ (max_cons_set_in_all_wrlds c)).2, 
      apply and.elim_right, apply cons_ctx_tt_iff_and.1, 
        apply ctx_tt_to_subctx_tt,
          apply ctx_is_tt (ext_ctx_to_max_set (Γ ⸴ ~p)),
            apply max_cons_set_in_all_wrlds c,
            apply ctx_is_subctx_of_max_ext,
    
    --to do: what if (Γ⊬ᵢ p) but (Γ ⊢ᵢ ~~p) ?
end
