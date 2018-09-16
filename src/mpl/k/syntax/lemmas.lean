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
   contradiction
end

/- full necessitation -/

def full_nec {Γ : ctx σ} {p : form σ} :
  (· ⊢ₖ p) ⇒ (Γ ⊢ₖ ◻p) :=
begin
  intro h,
  induction Γ,
    apply nec,
      reflexivity,
      assumption,
    apply necwk Γ_ih
end

/- structural rules -/

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
    apply necwk,
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
    contradiction
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
    contradiction
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
    apply full_nec,
      induction h_cnil,
        assumption,
end

def subctx_contr {Γ Δ : ctx σ} {p : form σ}:
   Δ ⊆ Γ ⇒ (Γ ⊔ Δ ⊢ₖ p) ⇒ (Γ ⊢ₖ p) :=
begin
  intros s h,
  induction h,
    cases (list.mem_append.1 h_h),
      exact prf.ax h,
      exact prf.ax (s h),
    exact prf.pl1 _,
    exact prf.pl2 _,
    exact prf.pl3 _,
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp,
    exact prf.k _,
    apply full_nec,
      induction h_cnil,
        assumption,
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
    contradiction
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
    contradiction
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

def dne {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₖ (~~p) ⊃ p :=
have h : Γ ⊢ₖ (~~p) ⊃ ((~p) ⊃ (~p)) := prf.mp (prf.pl1 _) id,
prf.mp (prf.mp (prf.pl2 Γ) (cut (prf.pl1 Γ) (prf.pl3 Γ))) h

def dni {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₖ p ⊃ (~~p) :=
prf.mp contrap dne 

def lem {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₖ  p ∨ (~p) :=
prf.mp dni (prf.mp contrap dne)

/-def nimpl_to_and {p q : form σ} {Γ : ctx σ} :
  Γ ⊢ₖ (~(p ⊃ q)) ⊃ (p & (~q)) :=
begin
  repeat {apply deduction},
    apply (prf.mp pr1),
      apply deduction,
        apply prf.mp, apply dne,
          exact (prf.mp pr1 pr2),
end-/

def not_impl_to_and_not {p q : form σ} {Γ : ctx σ} :
  Γ ⊢ₖ (~(p ⊃ q)) ⊃ (p & ~q) :=
begin
  repeat { apply deduction },
    apply prf.mp,
      exact pr1,
      apply deduction,
        apply prf.mp,
          apply dne,
          apply prf.mp,
            exact pr1,
            exact pr2
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

def impl_weak {p q r : form σ} {Γ : ctx σ} (h : (Γ ⸴ r ⊢ₖ p) ⇒ (Γ ⊢ₖ p)) :
  ((Γ ⊢ₖ p) ⇒ (Γ ⊢ₖ q)) ⇒ ((Γ ⸴ r ⊢ₖ p) ⇒ (Γ ⸴ r ⊢ₖ q)) :=
λ hpq hp, weak (hpq (h hp))

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

end prf
