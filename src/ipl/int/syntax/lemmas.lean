/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic

variable {σ : nat}

namespace prf

/- identity implication -/

def id {p : form σ} {Γ : ctx σ} :
  Γ ⊢ᵢ p ⊃ p :=
prf.mp (prf.mp (@prf.pl2 σ Γ p (p ⊃ p) p) (prf.pl1 Γ)) (prf.pl1 Γ)

/- deduction metatheorem -/

def deduction {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⊢ᵢ q) ⇒ (Γ ⊢ᵢ p ⊃ q) :=
begin
 intro h,
 induction h,
   cases h_h,
     induction h_h,
       exact id,
       exact prf.mp (prf.pl1 Γ)  (prf.ax h_h),
   exact prf.mp (prf.pl1 Γ) (prf.pl1 Γ),
   exact prf.mp (prf.pl1 _) (prf.pl2 _),
   repeat {
     apply prf.mp, apply prf.pl1,
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
   apply prf.mp,
     exact (prf.mp (prf.pl2 _) h_ih_hpq),
     exact h_ih_hp
end

/- structural rules -/

def union_weak_left {Γ Δ : ctx σ} {p : form σ} :
  (Γ ⊢ᵢ p) ⇒ (Γ ⊔ Δ ⊢ᵢ p) :=
begin
  intro h,
  induction h,
    apply prf.ax,
      exact (mem_ext_append_left h_h),
    exact prf.pl1 _,
    exact prf.pl2 _,
    repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def union_weak_right {Γ Δ : ctx σ} {p : form σ} :
  (Γ ⊢ᵢ p) ⇒ (Δ ⊔ Γ ⊢ᵢ p) :=
begin
  intro h,
  induction h,
    apply prf.ax,
      exact (mem_ext_append_right h_h),
    exact prf.pl1 _,
    exact prf.pl2 _,
    repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def sub_weak {Γ Δ : ctx σ} {p : form σ} :
  (Δ ⊢ᵢ p) ⇒ (Δ ⊆ Γ) ⇒ (Γ ⊢ᵢ p) :=
begin
  intros h s,
  induction h,
    apply prf.ax,
      exact s h_h,
    exact prf.pl1 _,
    exact prf.pl2 _,
    repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def weak {Γ : ctx σ} {p q : form σ} :
  (Γ ⊢ᵢ p) ⇒ (Γ ⸴ q ⊢ᵢ p) :=
begin
  intro h,
  induction h,
    apply prf.ax,
      exact (mem_ext_cons_left h_h),
    exact prf.pl1 _,
    exact prf.pl2 _,
    repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def full_contr {Γ Δ : ctx σ} {p : form σ} :
  (Γ ⊔ Δ ⊔ Δ ⊢ᵢ p) ⇒ (Γ ⊔ Δ ⊢ᵢ p) :=
begin
  intro h,
  induction h,
    apply prf.ax,
      apply or.elim h_h,
        intro, assumption,
        apply mem_ext_append_right,
    exact prf.pl1 _,
    exact prf.pl2 _,
    repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def contr {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⸴ p ⊢ᵢ q) ⇒ (Γ ⸴ p ⊢ᵢ q) :=
begin
  intro h,
  induction h,
    apply prf.ax,
      apply mem_contr_cons_right,
        exact h_h,
    exact prf.pl1 _,
    exact prf.pl2 _,
    repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def full_exg {Γ Δ : ctx σ} {p : form σ} :
  (Γ ⊔ Δ ⊢ᵢ p) ⇒ (Δ ⊔ Γ ⊢ᵢ p) :=
begin
  intro h,
  induction h,
    apply prf.ax,
      apply mem_exg_append_right,
        exact h_h,
    exact prf.pl1 _,
    exact prf.pl2 _,
    repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def exg {p q r : form σ} {Γ : ctx σ} :
  (Γ ⸴ p ⸴ q ⊢ᵢ r) ⇒ (Γ ⸴ q ⸴ p ⊢ᵢ r) :=
begin
  intro h,
  induction h,
    apply prf.ax,
      apply mem_exg_cons_right,
        exact h_h,
    exact prf.pl1 _,
    exact prf.pl2 _,
    repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def exg_left {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⊢ᵢ q) ⇔ ({p} ⊔ Γ ⊢ᵢ q) :=
begin
  apply iff.intro,
    intro h,
    induction h,
      apply prf.ax,
        cases h_h,
         induction h_h,
           apply trivial_mem_right,
           apply mem_ext_cons_right,
             exact h_h,
      exact prf.pl1 _,
      exact prf.pl2 _,
      repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
      apply prf.mp,
        exact h_ih_hpq,
        exact h_ih_hp,
    intro h,
    induction h,
      apply prf.ax,
        cases h_h,
          cases h_h,
            induction h_h,
              apply trivial_mem_left,
              apply false.rec, assumption,
          apply mem_ext_cons_left, assumption,
      exact prf.pl1 _,
      exact prf.pl2 _,
      repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
      apply prf.mp,
        exact h_ih_hpq,
        exact h_ih_hp,
end

/- subcontext operations -/

def subctx_ax {Γ Δ : ctx σ} {p : form σ} :
   Δ ⊆ Γ ⇒ (Δ ⊢ᵢ p) ⇒ (Γ ⊢ᵢ p) :=
begin
  intros s h,
  induction h,
    apply prf.ax (s h_h),            
    exact prf.pl1 _,
    exact prf.pl2 _,
    repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def subctx_contr {Γ Δ : ctx σ} {p : form σ}:
   Δ ⊆ Γ ⇒ (Γ ⊔ Δ ⊢ᵢ p) ⇒ (Γ ⊢ᵢ p) :=
begin
  intros s h,
  induction h,
    cases h_h,
      exact prf.ax h_h,
      exact prf.ax (s h_h),
    exact prf.pl1 _,
    exact prf.pl2 _,
    repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

/- right-hand side basic rules of inference -/

def pr {Γ : ctx σ} {p : form σ} :
  Γ ⸴ p ⊢ᵢ p :=
by apply ax; apply or.intro_left; simp

def pr1 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⸴ q ⊢ᵢ p :=
by apply ax; apply or.intro_right; apply or.intro_left; simp

def pr2 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⸴ q ⊢ᵢ q :=
by apply ax; apply or.intro_left; simp

def by_mp1 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⸴ p ⊃ q ⊢ᵢ q :=
prf.mp pr2 pr1

def by_mp2 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⊃ q ⸴ p ⊢ᵢ q :=
prf.mp pr1 pr2

def cut {Γ : ctx σ} {p q r : form σ} :
  (Γ ⊢ᵢ p ⊃ q) ⇒ (Γ ⊢ᵢ q ⊃ r) ⇒ (Γ ⊢ᵢ p ⊃ r) :=
λ H1 H2, prf.mp (prf.mp (prf.pl2 _) (prf.mp (prf.pl1 _) H2 )) H1

def conv_deduction {Γ : ctx σ} {p q : form σ} :
  (Γ ⊢ᵢ p ⊃ q) ⇒ (Γ ⸴ p ⊢ᵢ q) :=
λ h, prf.mp (weak h) pr 

/- left-hand side basic rules of inference -/

def mp_in_ctx_left {Γ : ctx σ} {p q r : form σ} :
  (Γ ⸴ p ⸴ q ⊢ᵢ r) ⇒ (Γ ⸴ p ⸴ p ⊃ q ⊢ᵢ r) :=
begin
  intro h,
  induction h,
    cases h_h,
      induction h_h,
        exact by_mp1,
      cases h_h,
        induction h_h,
          exact pr1,
        apply prf.ax,
          apply mem_ext_cons_left,
            apply mem_ext_cons_left,
              exact h_h,
    exact prf.pl1 _,
    exact prf.pl2 _,
    repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def mp_in_ctx_right {Γ : ctx σ} {p q r : form σ} :
  (Γ ⸴ p ⸴ p ⊃ q ⊢ᵢ r) ⇒ (Γ ⸴ p ⸴ q ⊢ᵢ r) :=
begin
  intro h,
  induction h,
    cases h_h,
      apply eq.subst,
        exact (eq.symm h_h),
        exact (prf.mp (prf.pl1 _) pr2),
      cases h_h,
        induction h_h,
          exact pr1,
        apply prf.ax,
          apply mem_ext_cons_left,
            apply mem_ext_cons_left,
              exact h_h,
    exact prf.pl1 _,
    exact prf.pl2 _,
    repeat {
     apply prf.andr <|> apply prf.andl <|> apply prf.andi <|>
     apply prf.orr <|> apply prf.orl <|> apply prf.ore <|> apply prf.falso},
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

/- basic lemmas -/

def not_impl {Γ : ctx σ} {p q : form σ} : 
  Γ ⊢ᵢ (p ⊃ q) ⊃ ((~q) ⊃ (~p)) :=
begin
  repeat {apply prf.deduction},
  apply prf.mp,
    exact prf.pr1,
      apply prf.mp,
        apply prf.ax,
          apply mem_ext_cons_left, apply mem_ext_cons_left,
            exact trivial_mem_left,
        exact prf.pr2
end

def impl_falso {Γ : ctx σ} {p q : form σ} : 
  Γ ⊢ᵢ (~p) ⊃ ((~q) ⊃ (p ⊃ q)) :=
begin
  repeat {apply prf.deduction},
  apply prf.mp, apply prf.falso,
    apply prf.mp, apply prf.ax,
      apply mem_ext_cons_left, apply mem_ext_cons_left, apply trivial_mem_left,
      apply prf.pr2
end

end prf


def dni {p : form σ} {Γ : ctx σ} :
  Γ ⊢ᵢ p ⊃ (~~p) :=
begin
  apply prf.deduction, apply prf.deduction,
    apply prf.mp, apply prf.pr2, apply prf.pr1 
end

def and_not_not_to_not_or {p q : form σ} {Γ : ctx σ} :
  Γ ⊢ᵢ ((~p) & (~q)) ⊃ ~(p ∨ q) :=
begin
  apply prf.deduction, apply prf.mp, apply prf.mp, apply prf.ore,
  apply prf.mp, apply prf.andr, exact ~q, apply prf.pr,
  apply prf.mp, apply prf.andl, exact ~p, apply prf.pr
end

