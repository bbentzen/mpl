/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .soundness .syntax.lemmas .semantics.lemmas ..misc

open classical

variables {σ : nat}

/- useful facts about consistency -/

def is_consist (Γ : ctx σ) : Prop := Γ ⊬ₖ ⊥

def not_prvb_to_consist {Γ : ctx σ} {p : form σ} :
  (Γ ⊬ₖ p) ⇒ is_consist Γ :=
λ nhp nc, nhp (prf.ex_falso nc)

def not_prvb_to_neg_consist {Γ : ctx σ} {p : form σ} :
  (Γ ⊬ₖ p) ⇒ is_consist (Γ ⸴ ~p) :=
λ hnp hc, hnp (prf.mp prf.dne (prf.deduction hc))

def inconsist_to_neg_consist {Γ : ctx σ} {p : form σ} :
  is_consist Γ ⇒ ¬is_consist (Γ ⸴ p) ⇒ is_consist (Γ ⸴ ~p) :=
begin
  intros c nc hp, apply c, apply prf.mp,
    apply prf.deduction, apply by_contradiction nc,
    apply prf.mp prf.dne, exact (prf.deduction hp),
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
  is_consist Γ  ⇒ (Γ ⊬ₖ ~p) ⇒ is_consist (Γ ⸴ p) :=
by intros c np hn; apply np (prf.deduction hn)

def inconsist_ext_to_inconsist {Γ : ctx σ} {p : form σ} :
    ((¬is_consist (Γ ⸴ p)) ∧ ¬is_consist(Γ ⸴ ~p)) ⇒ ¬is_consist (Γ) :=
begin
  intros h nc, cases h,
  have h1 : ((Γ ⸴ p) ⊢ₖ ⊥) := by_contradiction h_left,
  have h2 : ((Γ ⸴ ~p) ⊢ₖ ⊥) := by_contradiction h_right,
  apply nc, apply prf.mp (prf.deduction h1),
    apply prf.mp prf.dne (prf.deduction h2)
end

def consist_to_consist_ext {Γ : ctx σ} {p : form σ} :
    is_consist (Γ) ⇒ (is_consist (Γ ⸴ p) ∨ is_consist (Γ ⸴ ~p)) :=
begin
  intro c, apply by_contradiction, intro h, 
    apply absurd c, apply inconsist_ext_to_inconsist,
      apply (decidable.not_or_iff_and_not _ _).1, apply h,
        repeat {apply (prop_decidable _)}
end

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

def tt_to_const {Γ : ctx σ} {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿) σ} {w : ctx σ} :
  (M⦃Γ⦄w) = tt ⇒ is_consist Γ :=
begin
  intros h hin,
  cases (sndnss hin),
    apply bot_is_insatisf,
      apply exists.intro,
        exact (m M w h),
        repeat {assumption}
end
