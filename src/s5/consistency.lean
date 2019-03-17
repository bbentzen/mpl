/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .soundness 

open prf classical

variables {σ : nat}

def is_consist (Γ : ctx σ) := Γ ⊬ₛ₅ ⊥

lemma consist_not_of_not_prf {Γ : ctx σ} {p : form σ} :
  (Γ ⊬ₛ₅ p) → is_consist (Γ ⸴ ~p) :=
λ hnp hc, hnp (mp dne (deduction hc))

lemma not_prf_of_consist_not {Γ : ctx σ} {p : form σ} :
  is_consist (Γ ⸴ ~p) → (Γ ⊬ₛ₅ p) :=
λ h c, h (conv_deduction (prf.mp prf.dni c))

/- other notable properties of consistency -/

lemma consist_of_not_prf {Γ : ctx σ} {p : form σ} : 
  (Γ ⊬ₛ₅ p) → is_consist Γ :=
λ nhp nc, nhp (ex_falso nc)

lemma inconsist_to_neg_consist {Γ : ctx σ} {p : form σ} :
  is_consist Γ → ¬is_consist (Γ ⸴ p) → is_consist (Γ ⸴ ~p) :=
begin
  intros c nc hp, apply c, apply mp,
    apply deduction, apply by_contradiction nc,
    apply mp dne, exact (deduction hp),
end

lemma inconsist_of_neg_to_consist {Γ : ctx σ} {p : form σ} :
  is_consist Γ → ¬is_consist (Γ ⸴ ~p) → is_consist (Γ ⸴ p) :=
begin
  intros c nc hp, apply c, apply mp,
  { apply deduction (by_contradiction nc) },
  { exact deduction hp },
end

lemma consist_fst {Γ : ctx σ} {p : form σ} :
  is_consist (Γ ⸴ p) → is_consist Γ :=
λ hc hn,  hc (weak hn)

/- consistent context extensions -/

lemma consist_ext {Γ : ctx σ} {p : form σ} :
  is_consist Γ  → (Γ ⊬ₛ₅ ~p) → is_consist (Γ ⸴ p) :=
by intros c np hn; apply np (deduction hn)

lemma inconsist_ext_to_inconsist {Γ : ctx σ} {p : form σ} :
    ((¬is_consist (Γ ⸴ p)) ∧ ¬is_consist(Γ ⸴ ~p)) → ¬is_consist (Γ) :=
begin
  intros h nc, cases h,
  have h₁ : ((Γ ⸴ p) ⊢ₛ₅ ⊥) := by_contradiction h_left,
  have h₂ : ((Γ ⸴ ~p) ⊢ₛ₅ ⊥) := by_contradiction h_right,
  apply nc, apply mp (deduction h₁),
    apply mp dne (deduction h₂)
end

lemma consist_to_consist_ext {Γ : ctx σ} {p : form σ} :
    is_consist (Γ) → (is_consist (Γ ⸴ p) ∨ is_consist (Γ ⸴ ~p)) :=
begin
  intro c, apply classical.by_contradiction, intro h, 
  apply absurd c, apply inconsist_ext_to_inconsist,
  apply (decidable.not_or_iff_and_not _ _).1, apply h,
  repeat {apply (prop_decidable _)}
end

lemma pos_consist_mem {Γ : ctx σ} {p : form σ} :
  p ∈ Γ → is_consist (Γ) → (~p) ∉ Γ :=
λ hp hc hnp, hc (mp (ax hnp) (ax hp))

lemma neg_consist_mem {Γ : ctx σ} {p : form σ} :
  (~p) ∈ Γ → is_consist (Γ) → p ∉ Γ :=
λ hnp hc hp, hc (mp (ax hnp) (ax hp))

lemma pos_inconsist_ext {Γ : ctx σ} {p : form σ} (c : is_consist Γ) :
  p ∈ Γ → ¬is_consist (Γ ⸴ p) → (~p) ∈ Γ :=
begin
  intros hp hn,
  exfalso, apply c,
  apply mp, apply deduction (by_contradiction hn),
  apply ax hp
end

lemma neg_inconsist_ext {Γ : ctx σ} {p : form σ} (c : is_consist Γ) :
  (~p) ∈ Γ → ¬is_consist (Γ ⸴ ~p) → p ∈ Γ :=
begin
  intros hp hn,
  exfalso, apply c,
  apply mp, apply deduction (by_contradiction hn),
  apply ax hp
end

/- context extensions of subcontexts -/

lemma sub_preserves_consist {Γ Δ : ctx σ} :
  is_consist Γ  → is_consist Δ → Δ ⊆ Γ → is_consist (Γ ⊔ Δ) :=
by intros c1 c2 s nc; apply c1; exact (subctx_contr s nc)

lemma subctx_inherits_consist {Γ Δ : ctx σ} {p : form σ} :
  is_consist Γ  → is_consist Δ → Γ ⊆ Δ → is_consist (Δ ⸴ p) → is_consist (Γ ⸴ p) :=
by intros c1 c2 s c nc; apply c; apply conv_deduction; apply subctx_ax s (deduction nc)

lemma inconsist_sub {Γ Δ : ctx σ} {p : form σ} (c : is_consist Γ) :
  ¬is_consist (Δ ⸴ p) → Δ ⊆ Γ → ¬is_consist (Γ ⸴ p) :=
begin
  unfold is_consist, intros h s c, apply c,
  apply subctx_ax, apply set.insert_subset_insert s,
  apply classical.by_contradiction h
end

/- contradictions & interpretations -/

lemma tt_to_const {Γ : ctx σ} {M : model} {w ∈ M.wrlds} :
  (w ⊩⦃M⦄ Γ) = tt → is_consist Γ :=
begin
  intros h hin,
  cases (sndnss hin),
  apply bot_is_insatisf,
  apply exists.intro,
  refine (m M w _ h),
  repeat {assumption},
end