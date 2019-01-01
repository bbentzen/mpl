/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .soundness

variables {σ : nat}

def is_consist (Γ : ctx σ) : Prop := Γ ⊬ₚ ⊥

/- useful facts about consistency -/

def not_prvb_to_consist {Γ : ctx σ} {p : form σ} :
  (Γ ⊬ₚ p) ⇒ is_consist Γ :=
by apply contrap.1; exact prf.ex_falso

def not_prvb_to_neg_consist {Γ : ctx σ} {p : form σ} :
  (Γ ⊬ₚ p) ⇒ is_consist (Γ ⸴ ~p) :=
λ hnp hc, hnp (prf.mp prf.dne (prf.deduction hc))

def contrad_not_consist_left {Γ : ctx σ} {p : form σ} :
  ¬is_consist (Γ ⸴ p ⸴ ~p) :=
λ hc, hc (prf.mp prf.pr2 prf.pr1)

def contrad_not_consist_right {Γ : ctx σ} {p : form σ} :
  ¬is_consist (Γ ⸴ ~p ⸴ p) :=
λ hc, hc (prf.mp prf.pr1 prf.pr2)

def not_consist_to_bot {Γ : ctx σ} :
  ¬is_consist Γ ⇒ (Γ ⊢ₚ ⊥) :=
begin
  intro hc, cases (classical.em _),
    assumption, contradiction
end

def mem_not_consist {Γ : ctx σ} {p : form σ} :
  p ∈ Γ ⇒ (~p) ∈ Γ ⇒ ¬is_consist Γ  :=
begin
  intros pm npm nc, apply false.rec, apply nc, 
    apply prf.mp, repeat {apply prf.ax, assumption}
end

def mem_not_consist_neg {Γ : ctx σ} {p : form σ} :
  p ∈ Γ ⇒ ¬is_consist (Γ ⸴ ~p)  :=
begin
  intros pm hc, apply hc,
  apply prf.mp,
    apply prf.pr,
    apply prf.weak,
      apply prf.ax,
        assumption
end

def mem_neg_not_consist {Γ : ctx σ} {p : form σ} :
  (~p) ∈ Γ ⇒ ¬is_consist (Γ ⸴ p)  :=
begin
  intros pm hc, apply hc,
  apply prf.mp,
    apply prf.weak,
      apply prf.ax,
        assumption,
    apply prf.pr,
end

def inconsist_to_neg_consist {Γ : ctx σ} {p : form σ} :
  is_consist Γ ⇒ ¬is_consist (Γ ⸴ p) ⇒ is_consist (Γ ⸴ ~p) :=
begin
  intros c nc hp, apply c, apply prf.mp,
    apply prf.deduction, apply classical.by_contradiction nc,
    apply prf.mp prf.dne, exact (prf.deduction hp),
end

def inconsist_of_neg_to_consist {Γ : ctx σ} {p : form σ} :
  is_consist Γ ⇒ ¬is_consist (Γ ⸴ ~p) ⇒ is_consist (Γ ⸴ p) :=
begin
  intros c nc hp, apply c, apply prf.mp,
    apply prf.deduction, apply classical.by_contradiction nc,
    exact (prf.deduction hp),
end

def consist_exg {Γ : ctx σ} {p q : form σ} : 
  is_consist (Γ ⸴ p ⸴ q) ⇒ is_consist (Γ ⸴ q ⸴ p) :=
begin
  intros hc hn,
  apply hc, apply prf.exg,
    assumption
end

def inconsist_exg {Γ : ctx σ} {p q : form σ} : 
  ¬is_consist (Γ ⸴ p ⸴ q) ⇒ ¬is_consist (Γ ⸴ q ⸴ p) :=
by apply contrap.1; exact consist_exg

/- consistency and derivability -/

def consist_proves_consist {Γ : ctx σ} {p : form σ} :
  is_consist Γ ⇒ (Γ ⊢ₚ p) ⇒ is_consist (Γ ⸴ p) :=
λ hc hp nc, hc (prf.mp (prf.deduction nc) hp)

def consist_clsd_impl {Γ : ctx σ} {p q : form σ} :
  is_consist (Γ ⸴ p) ⇒ (Γ ⊢ₚ p ⊃ q) ⇒ is_consist (Γ ⸴ q) :=
begin
  unfold is_consist,
  intros hc hpq nc, apply hc,
    apply prf.conv_deduction,
      apply prf.mp,
        apply prf.mp prf.not_impl hpq,
        apply prf.deduction, assumption
end

def consist_not_prvb_neg {Γ : ctx σ} {p q : form σ} :
  (is_consist (Γ ⸴ p ⸴ ~q)) ⇒ (Γ ⸴ p ⊬ₚ q) :=
begin
  unfold is_consist, intros hc hq,
  apply hc, apply prf.mp,
    apply prf.pr,
    apply prf.weak hq
end

/- strenghtening -/

def ctx_removable {Γ : ctx σ} {p : form σ} :
  (Γ ⊢ₚ p) ⇒ is_consist (Γ ⸴ ~p) ⇒ (· ⊢ₚ p) :=
begin
  intros h hc,
    induction h,
      apply prf.ax, 
        apply mem_not_consist_neg,
          repeat {assumption},

      exact prf.pl1 _,
      exact prf.pl2 _,
      exact prf.pl3 _,

      apply false.rec,
        apply hc, apply prf.conv_deduction,
          apply prf.mp, apply prf.dni,
            apply prf.mp,
              repeat {assumption}
end

/- notable projections -/

def consist_fst {Γ : ctx σ} {p : form σ} :
  is_consist (Γ ⸴ p) ⇒ is_consist Γ :=
λ hc hn,  hc (prf.weak hn)

def consist_snd {Γ : ctx σ} {p : form σ} :
  is_consist (Γ ⸴ p) ⇒ is_consist {p} :=
begin
  intros hc hn,
  apply hc,
    apply iff.elim_right,
      exact prf.exg_left,
    apply prf.union_weak_left,
      exact hn
end

/- consistent context extensions -/

def consist_ext {Γ : ctx σ} {p : form σ} :
  is_consist Γ  ⇒ (Γ ⊬ₚ ~p) ⇒ is_consist (Γ ⸴ p) :=
by intros c np hn; apply np (prf.deduction hn)

def inconsist_ext_to_inconsist {Γ : ctx σ} {p : form σ} :
    ((¬is_consist (Γ ⸴ p)) ∧ ¬is_consist(Γ ⸴ ~p)) ⇒ ¬is_consist (Γ) :=
begin
  intros h nc, cases h,
  have h1 : ((Γ ⸴ p) ⊢ₚ ⊥) := classical.by_contradiction h_left,
  have h2 : ((Γ ⸴ ~p) ⊢ₚ ⊥) := classical.by_contradiction h_right,
  apply nc, apply prf.mp (prf.deduction h1),
    apply prf.mp prf.dne (prf.deduction h2)
end

def consist_to_consist_ext {Γ : ctx σ} {p : form σ} :
    is_consist (Γ) ⇒ (is_consist (Γ ⸴ p) ∨ is_consist (Γ ⸴ ~p)) :=
begin
  intro c, apply classical.by_contradiction, intro h, 
    apply absurd c, apply inconsist_ext_to_inconsist,
      apply (decidable.not_or_iff_and_not _ _).1, apply h,
        repeat {apply (classical.prop_decidable _)}
end

def pos_inconsist_ext {Γ : ctx σ} {p : form σ} (c : is_consist Γ) :
  p ∈ Γ ⇒ ¬is_consist (Γ ⸴ p) ⇒ (~p) ∈ Γ :=
begin
  intros hp hn,
  apply false.elim, apply c,
    apply prf.mp, apply prf.deduction (classical.by_contradiction hn),
    apply prf.ax hp
end

def neg_inconsist_ext {Γ : ctx σ} {p : form σ} (c : is_consist Γ) :
  (~p) ∈ Γ ⇒ ¬is_consist (Γ ⸴ ~p) ⇒ p ∈ Γ :=
begin
  intros hp hn,
  apply false.elim, apply c,
    apply prf.mp, apply prf.deduction (classical.by_contradiction hn),
    apply prf.ax hp
end

/- context extensions of subcontexts -/

def sub_preserves_consist {Γ Δ : ctx σ} :
  is_consist Γ  ⇒ Δ ⊆ Γ ⇒ is_consist Δ :=
by intros hc sub nc; apply hc; apply prf.sub_weak nc; assumption

def sub_preserves_consist_union {Γ Δ : ctx σ} :
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

def tt_to_const {v : var σ → bool} {Γ : ctx σ} {p : form σ} : 
  (⦃Γ⦄ v) = tt ⇒ is_consist Γ :=
begin
  intros h hin,
  cases (sndnss hin),
    apply bot_is_insatisf,
      apply exists.intro,
        exact (m v h)
end

/- notable consistent & inconsistent sets -/

def theory_is_consist : @is_consist σ · :=
begin
  intro h, cases (sndnss h),
    apply bot_is_insatisf, 
      apply exists.intro, apply m,
        unfold ctx_tt_in_val, simp, intros, exact ff
end

def pos_literal_is_consist {v : var σ} : @is_consist σ {#v} :=
begin
  intro h, cases (sndnss h),
  apply bot_is_insatisf, 
    apply exists.intro, apply m (λ v, tt),
        unfold ctx_tt_in_val, simp, unfold form_tt_in_val
end

def neg_literal_is_consist {v : var σ} : @is_consist σ {~#v} :=
begin
  intro h, cases (sndnss h),
  apply bot_is_insatisf, 
    apply exists.intro, apply m (λ v, ff),
        unfold ctx_tt_in_val, simp, unfold form_tt_in_val, simp
end

def bot_is_inconsist : ¬(@is_consist σ {⊥}) :=
begin
  intro h, apply h, exact prf.pr
end
