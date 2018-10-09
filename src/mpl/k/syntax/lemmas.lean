/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic .context.lemmas

variable {σ : nat}

namespace prf

/- identity implication -/

def id {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₖ p ⊃ p :=
prf.mp (prf.mp (@prf.pl2 σ Γ p (p ⊃ p) p) (prf.pl1 Γ)) (prf.pl1 Γ)

/- deduction metatheorem -/

def deduction {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⊢ₖ q) ⇒ (Γ ⊢ₖ p ⊃ q) :=
begin
 intro h,
 induction h,
   cases h_h,
     induction h_h,
       exact id,
       exact prf.mp (prf.pl1 Γ)  (prf.ax h_h),
   exact prf.mp (prf.pl1 Γ) (prf.pl1 Γ),
   exact prf.mp (prf.pl1 _) (prf.pl2 _),
   exact prf.mp (prf.pl1 _) (prf.pl3 _),
   apply prf.mp,
     exact (prf.mp (prf.pl2 _) h_ih_hpq),
     exact h_ih_hp,
  exact prf.mp (prf.pl1 _) (prf.k _),
  apply false.rec, apply has_append_ctx_not_empty, assumption
end

/- the full necessitation rule -/

def full_nec {Γ : ctx σ} {p : form σ} :
  (· ⊢ₖ p) ⇒ (Γ ⊢ₖ ◻p) :=
begin
  intro h,
    apply nec_weak,
      exact empty_sub_every_ctx,
      apply prf.nec,
        reflexivity,
        assumption
end

/- structural rules -/

def sub_weak {Γ Δ : ctx σ} {p : form σ} :
  (Δ ⊢ₖ p) ⇒ (Δ ⊆ Γ) ⇒ (Γ ⊢ₖ p) :=
begin
  intros h s,
  induction h,
    apply prf.ax,
      exact s h_h,
    exact prf.pl1 _,
    exact prf.pl2 _,
    exact prf.pl3 _,
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp,
    exact prf.k _,
    apply nec_weak s,
      apply prf.nec,
        induction h_cnil,
          reflexivity,
          assumption
end

def weak {Γ : ctx σ} {p q : form σ} :
  (Γ ⊢ₖ p) ⇒ (Γ ⸴ q ⊢ₖ p) :=
begin
  intro h,
  induction h,
    apply prf.ax,
      exact (mem_ext_cons_left h_h),
    exact prf.pl1 _,
    exact prf.pl2 _,
    exact prf.pl3 _,
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp,
    exact prf.k _,
    apply nec_weak,
      intro, apply mem_ext_cons_left,
      apply prf.nec,
        induction h_cnil,
          reflexivity,
          assumption
end

def contr {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⸴ p ⊢ₖ q) ⇒ (Γ ⸴ p ⊢ₖ q) :=
begin
  intro h,
  induction h,
    apply prf.ax,
      apply mem_contr_cons_right,
        exact h_h,
    exact prf.pl1 _,
    exact prf.pl2 _,
    exact prf.pl3 _,
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp,
    exact prf.k _,
    apply false.rec, apply has_append_ctx_not_empty, assumption
end

def exg {p q r : form σ} {Γ : ctx σ} :
  (Γ ⸴ p ⸴ q ⊢ₖ r) ⇒ (Γ ⸴ q ⸴ p ⊢ₖ r) :=
begin
  intro h,
  induction h,
    apply prf.ax,
      apply mem_exg_cons_right,
        exact h_h,
    exact prf.pl1 _,
    exact prf.pl2 _,
    exact prf.pl3 _,
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp,
    exact prf.k _,
    apply false.rec, apply has_append_ctx_not_empty, assumption
end

/- subcontext operations -/

def subctx_ax {Γ Δ : ctx σ} {p : form σ} :
   Δ ⊆ Γ ⇒ (Δ ⊢ₖ p) ⇒ (Γ ⊢ₖ p) :=
begin
  intros s h,
  induction h,
    apply prf.ax (s h_h),            
    exact prf.pl1 _,
    exact prf.pl2 _,
    exact prf.pl3 _,
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp,
    exact prf.k _,
    apply nec_weak s,
      cases h_cnil,
        apply prf.nec,
          reflexivity,
          assumption 
end

def subctx_contr {Γ Δ : ctx σ} {p : form σ}:
   Δ ⊆ Γ ⇒ (Γ ⊔ Δ ⊢ₖ p) ⇒ (Γ ⊢ₖ p) :=
begin
  intros s h,
  induction h,
    cases h_h,
      exact prf.ax h_h,
      exact prf.ax (s h_h),
    exact prf.pl1 _,
    exact prf.pl2 _,
    exact prf.pl3 _,
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp,
    exact prf.k _,
    apply nec_weak s,
      revert h_h, rewrite h_cnil,
      apply full_nec
end

/- right-hand side basic rules of inference -/

def pr {Γ : ctx σ} {p : form σ} :
  Γ ⸴ p ⊢ₖ p :=
by apply ax; apply or.intro_left; simp

def pr1 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⸴ q ⊢ₖ p :=
by apply ax; apply or.intro_right; apply or.intro_left; simp

def pr2 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⸴ q ⊢ₖ q :=
by apply ax; apply or.intro_left; simp

def by_mp1 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⸴ p ⊃ q ⊢ₖ q :=
prf.mp pr2 pr1

def by_mp2 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⊃ q ⸴ p ⊢ₖ q :=
prf.mp pr1 pr2

def cut {Γ : ctx σ} {p q r : form σ} :
  (Γ ⊢ₖ p ⊃ q) ⇒ (Γ ⊢ₖ q ⊃ r) ⇒ (Γ ⊢ₖ p ⊃ r) :=
λ H1 H2, prf.mp (prf.mp (prf.pl2 _) (prf.mp (prf.pl1 _) H2 )) H1

def conv_deduction {Γ : ctx σ} {p q : form σ} :
  (Γ ⊢ₖ p ⊃ q) ⇒ (Γ ⸴ p ⊢ₖ q) :=
λ h, prf.mp (weak h) pr 

/- left-hand side basic rules of inference -/

def mp_in_ctx_left {Γ : ctx σ} {p q r : form σ} :
  (Γ ⸴ p ⸴ q ⊢ₖ r) ⇒ (Γ ⸴ p ⸴ p ⊃ q ⊢ₖ r) :=
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
    exact prf.pl3 _,
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp,
    exact prf.k _,
    apply false.rec, apply has_append_ctx_not_empty, assumption
end

def mp_in_ctx_right {Γ : ctx σ} {p q r : form σ} :
  (Γ ⸴ p ⸴ p ⊃ q ⊢ₖ r) ⇒ (Γ ⸴ p ⸴ q ⊢ₖ r) :=
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
    exact prf.pl3 _,
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp,
    exact prf.k _,
    apply false.rec, apply has_append_ctx_not_empty, assumption
end

/- basic lemmas -/

def contrap {Γ : ctx σ} {p q : form σ} :
  Γ ⊢ₖ ((~q) ⊃ (~p)) ⊃ (p ⊃ q) :=
deduction (deduction
  (prf.mp (prf.mp (prf.pl3 _)
    begin
      apply weak,
        apply ax,
          apply or.intro_left,
          simp 
    end
  ) 
  begin
    apply prf.mp,
      exact (prf.pl1 _),
      apply ax,
        apply or.intro_left,
        simp
   end 
  )
)

def not_impl {Γ : ctx σ} {p q : form σ} : 
  Γ ⊢ₖ (p ⊃ q) ⊃ ((~q) ⊃ (~p)) :=
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

def dne {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₖ (~~p) ⊃ p :=
have h : Γ ⊢ₖ (~~p) ⊃ ((~p) ⊃ (~p)) := prf.mp (prf.pl1 _) id,
prf.mp (prf.mp (prf.pl2 Γ) (cut (prf.pl1 Γ) (prf.pl3 Γ))) h

def dni {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₖ p ⊃ (~~p) :=
prf.mp contrap dne 

def lem {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₖ  p ∨ ~p :=
prf.mp dni (prf.mp contrap dne)

def not_impl_to_and {p q : form σ} {Γ : ctx σ} :
  Γ ⊢ₖ (~(p ⊃ q)) ⊃ (p & (~q)) :=
begin
  repeat {apply deduction},
    apply (prf.mp pr1),
      apply deduction,
        apply prf.mp, apply dne,
          exact (prf.mp pr1 pr2),
end

def and_not_to_not_impl {p q : form σ} {Γ : ctx σ} :
  Γ ⊢ₖ (p & (~q)) ⊃ ~(p ⊃ q) :=
begin
  repeat {apply deduction},
    apply prf.mp,
      apply prf.pr1,
      apply cut,
        apply prf.pr2,
        apply dni
end

/- notable introduction rules -/

def negintro {p q : form σ} {Γ : ctx σ} :
  (Γ ⊢ₖ p ⊃ q) ⇒ (Γ ⊢ₖ p ⊃ ~q) ⇒ (Γ ⊢ₖ ~p) :=
have h : ∀ q, (Γ ⊢ₖ p ⊃ q) ⇒ (Γ ⊢ₖ (~~p) ⊃ q) := λ q h, cut dne h,
  λ hp hnp, prf.mp (prf.mp (prf.pl3 _) (h (~q) hnp)) (h q hp)

def ex_falso {Γ : ctx σ} {p : form σ} :
  (Γ ⊢ₖ ⊥) ⇒ (Γ ⊢ₖ p) :=
begin
  intro h,
  apply prf.mp,
    exact dne,
    apply prf.mp,
      exact prf.pl1 _,
      exact h
end

def ex_falso_and {Γ : ctx σ} {p q : form σ} :
  Γ ⊢ₖ (~p) ⊃ (p ⊃ q) :=
begin
  repeat {apply deduction},
  apply ex_falso,
  exact (prf.mp pr1 pr2)
end

def ex_falso_pos {Γ : ctx σ} {p q : form σ} :
  Γ ⊢ₖ p ⊃ ((~p) ⊃ q) :=
begin
  repeat {apply deduction},
    apply prf.mp, apply prf.mp, apply ex_falso_and,
      exact (prf.pr2),
      exact (prf.pr1),
end

def contr_conseq {Γ : ctx σ} {p r : form σ} :
  Γ ⊢ₖ (p ⊃ r) ⊃ (((~p) ⊃ r) ⊃ r) :=
begin
  repeat {apply deduction},
    apply prf.mp, apply prf.mp,
      apply prf.pl3, exact p,
      apply prf.mp,
        apply not_impl,
        exact pr1,
      apply cut,
        apply prf.mp,
          apply not_impl,
            exact (~p),
          apply pr2,
        apply dne
end

def impl_weak {p q r : form σ} {Γ : ctx σ} (h : (Γ ⸴ r ⊢ₖ p) ⇒ (Γ ⊢ₖ p)) :
  ((Γ ⊢ₖ p) ⇒ (Γ ⊢ₖ q)) ⇒ ((Γ ⸴ r ⊢ₖ p) ⇒ (Γ ⸴ r ⊢ₖ q)) :=
λ hpq hp, weak (hpq (h hp))

def and_intro {Γ : ctx σ} {p q : form σ} :
  (Γ ⊢ₖ p) ⇒ (Γ ⊢ₖ q) ⇒ (Γ ⊢ₖ (p & q)) :=
begin
  intros hp hq, apply deduction,
    apply prf.mp,
      apply prf.mp,
        apply pr,
      repeat {apply weak, assumption}
end


def and_elim_left {p q : form σ} {Γ : ctx σ} :
  (Γ ⸴ (p & q) ⊢ₖ p) :=
begin
  apply prf.mp, apply dne,
    apply prf.mp,
      apply prf.mp,
        apply prf.pl2,
          exact (p ⊃ (q ⊃ ⊥)),
            apply prf.mp,
              apply prf.pl1,
              exact pr,
            exact ex_falso_and
end

def and_elim_right {p q : form σ} {Γ : ctx σ} :
  (Γ ⸴ (p & q) ⊢ₖ q) :=
begin
  apply prf.mp, apply dne,
    apply prf.mp,
      apply prf.mp,
        apply prf.pl2,
          exact (p ⊃ (q ⊃ ⊥)),
            apply prf.mp,
              apply prf.pl1,
              exact pr,
          repeat {apply deduction},
            apply prf.mp,
              apply prf.ax,
               apply mem_ext_cons_left, apply mem_ext_cons_left,
                 apply trivial_mem_left,
              exact pr2
end

def or_intro_left {Γ : ctx σ} {p q r : form σ} :
  (Γ ⊢ₖ p) ⇒ (Γ ⊢ₖ (p ∨ q)) :=
begin
  intros hp, simp,
  apply prf.mp, apply dni,
  apply deduction,
    apply prf.mp,
      apply prf.mp,
        apply ex_falso_and,
        exact pr,
        apply weak, assumption
end

def or_intro_right {Γ : ctx σ} {p q r : form σ} :
  (Γ ⊢ₖ q) ⇒ (Γ ⊢ₖ (p ∨ q)) :=
begin
  intros hp, simp,
  apply prf.mp, apply dni,
  apply deduction,
    apply prf.mp, apply dni,
      apply weak, assumption
end

def or_elim {Γ : ctx σ} {p q r : form σ} :
  (Γ ⊢ₖ (p ∨ q)) ⇒ (Γ ⊢ₖ p ⊃ r) ⇒ (Γ ⊢ₖ q ⊃ r) ⇒ (Γ ⊢ₖ r) :=
begin
  intros hpq hpr hqr,
  apply prf.mp, apply prf.mp,
    apply contr_conseq,
      exact p,
      assumption,
      apply cut,
        apply prf.mp,
          apply dne,
          assumption,
        apply cut,
          exact dne,
          assumption
end

def detach_pos {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⊢ₖ q) ⇒ (Γ ⸴ ~p ⊢ₖ q) ⇒ (Γ ⊢ₖ q) :=
begin
  intros hpq hnpq,
  apply or_elim, apply lem,
    repeat {apply deduction, assumption}
end

def detach_neg {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ ~p ⊢ₖ q) ⇒ (Γ ⸴ p ⊢ₖ q) ⇒ (Γ ⊢ₖ q) :=
begin
  intros hpq hnpq,
  apply or_elim, apply lem,
    apply deduction, exact hnpq,
    apply deduction, assumption
end


end prf