/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .soundness .syntax.lemmas .semantics.lemmas

open classical

variables {σ : nat}

/- useful facts about consistency -/

def is_consist (Γ : ctx σ) : Prop := Γ ⊬ᵢ  ⊥

def not_prvb_to_consist {Γ : ctx σ} {p : form σ} :
  (Γ ⊬ᵢ p) ⇒ is_consist Γ :=
begin
  intros nhp nc, apply nhp, apply prf.mp, apply prf.falso, assumption
end

def not_prvb_to_neg_consist {Γ : ctx σ} {p : form σ} :
  (Γ ⊬ᵢ ~~p) ⇒ is_consist (Γ ⸴ ~p) :=
begin
  intros nhp nc, apply nhp, apply prf.deduction nc, 
end

def inconsist_of_neg_to_consist {Γ : ctx σ} {p : form σ} :
  is_consist Γ ⇒ ¬is_consist (Γ ⸴ ~p) ⇒ is_consist (Γ ⸴ p) :=
begin
  intros c nc hp, apply c, apply prf.mp,
    apply prf.deduction, apply by_contradiction nc,
    exact (prf.deduction hp),
end

def consist_fst {Γ : ctx σ} {p : form σ} :
  is_consist (Γ ⸴ p) ⇒ is_consist Γ :=
λ hc hn,  hc (prf.weak hn)

/- consistent context extensions -/

def consist_ext {Γ : ctx σ} {p : form σ} :
  is_consist Γ  ⇒ (Γ ⊬ᵢ ~p) ⇒ is_consist (Γ ⸴ p) :=
by intros c np hn; apply np (prf.deduction hn)

def consist_to_consist_ext {Γ : ctx σ} {p : form σ} :
    is_consist (Γ) ⇒ (is_consist (Γ ⸴ p) ∨ is_consist (Γ ⸴ ~p)) :=
begin
  intro c, apply classical.by_contradiction, intro h, 
    apply absurd c, apply inconsist_ext_to_inconsist,
      apply (decidable.not_or_iff_and_not _ _).1, apply h,
        repeat {apply (prop_decidable _)}
end

def pos_consist_mem {Γ : ctx σ} {p : form σ} :
  p ∈ Γ ⇒ is_consist (Γ) ⇒ (~p) ∉ Γ :=
λ hp hc hnp, hc (prf.mp (prf.ax hnp) (prf.ax hp))

def neg_consist_mem {Γ : ctx σ} {p : form σ} :
  (~p) ∈ Γ ⇒ is_consist (Γ) ⇒ p ∉ Γ :=
λ hnp hc hp, hc (prf.mp (prf.ax hnp) (prf.ax hp))

def pos_inconsist_ext {Γ : ctx σ} {p : form σ} (c : is_consist Γ) :
  p ∈ Γ ⇒ ¬is_consist (Γ ⸴ p) ⇒ (~p) ∈ Γ :=
begin
  intros hp hn,
  apply false.elim, apply c,
    apply prf.mp, apply prf.deduction (by_contradiction hn),
    apply prf.ax hp
end

def neg_inconsist_ext {Γ : ctx σ} {p : form σ} (c : is_consist Γ) :
  (~p) ∈ Γ ⇒ ¬is_consist (Γ ⸴ ~p) ⇒ p ∈ Γ :=
begin
  intros hp hn,
  apply false.elim, apply c,
    apply prf.mp, apply prf.deduction (by_contradiction hn),
    apply prf.ax hp
end

/- deductive closure -/

def deriv_consist {Γ : ctx σ} {p : form σ} (c : is_consist Γ) :
  (Γ ⊢ᵢ p) → (Γ ⊬ᵢ ~p) :=
begin
  intros h hc,
  apply c, apply prf.mp hc h
end

/- context extensions of subcontexts -/

def sub_preserves_consist {Γ Δ : ctx σ} :
  is_consist Γ  ⇒ is_consist Δ ⇒ Δ ⊆ Γ ⇒ is_consist (Γ ⊔ Δ) :=
by intros c1 c2 s nc; apply c1; exact (prf.subctx_contr s nc)

def subctx_inherits_consist {Γ Δ : ctx σ} {p : form σ} :
  is_consist Γ  ⇒ is_consist Δ ⇒ Γ ⊆ Δ ⇒ is_consist (Δ ⸴ p) ⇒ is_consist (Γ ⸴ p) :=
by intros c1 c2 s c nc; apply c; apply prf.conv_deduction; apply prf.subctx_ax s (prf.deduction nc)

def inconsist_sub {Γ Δ : ctx σ} {p : form σ} (c : is_consist Γ) :
  ¬is_consist (Δ ⸴ p) ⇒ Δ ⊆ Γ ⇒ ¬is_consist (Γ ⸴ p) :=
begin
  unfold is_consist, intros h s c, apply c,
  apply prf.subctx_ax, apply sub_cons_left s,
  apply classical.by_contradiction h
end

/- contradictions & interpretations -/

def tt_to_const {Γ : ctx σ} {M : 𝓦 ⸴ 𝓡 ⸴ 𝓿} (w ∈ (𝓦 ▹ M)) (h_per : is_persistent M) :
  (M⦃Γ⦄w) = tt ⇒ is_consist Γ :=
begin
  intros h hin,
  cases (sndnss hin),
    apply bot_is_insatisf,
      apply exists.intro,
        apply m, repeat {assumption}
end
