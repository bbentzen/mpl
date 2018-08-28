/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic .context.lemmas

variable {σ : nat}

namespace prf

/- identity implication -/

def id {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₚ p ⊃ p :=
prf.mp (prf.mp (@prf.pl2 σ Γ p (p ⊃ p) p) (prf.pl1 Γ)) (prf.pl1 Γ)

/- deduction metatheorem -/

def deduction {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⊢ₚ q) ⇒ (Γ ⊢ₚ p ⊃ q) :=
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
     exact h_ih_hp
end

/- structural rules -/

def full_weak {Γ Δ : ctx σ} {p : form σ} :
  (Γ ⊢ₚ p) ⇒ (Γ ⊔ Δ ⊢ₚ p) :=
begin
  intro h,
  induction h,
    apply prf.ax,
      exact (mem_ext_append_left h_h),
    exact prf.pl1 _,
    exact prf.pl2 _,
    exact prf.pl3 _,
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def weak {Γ : ctx σ} {p q : form σ} :
  (Γ ⊢ₚ p) ⇒ (Γ ⸴ q ⊢ₚ p) :=
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
      exact h_ih_hp
end

def full_contr {Γ Δ : ctx σ} {p : form σ} :
  (Γ ⊔ Δ ⊔ Δ ⊢ₚ p) ⇒ (Γ ⊔ Δ ⊢ₚ p) :=
begin
  intro h,
  induction h,
    apply prf.ax,
      cases (list.mem_append.1 h_h),
        exact h,
        exact (mem_ext_append_right h),
    exact prf.pl1 _,
    exact prf.pl2 _,
    exact prf.pl3 _,
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def contr {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⸴ p ⊢ₚ q) ⇒ (Γ ⸴ p ⊢ₚ q) :=
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
      exact h_ih_hp
end

def full_exg {Γ Δ : ctx σ} {p : form σ} :
  (Γ ⊔ Δ ⊢ₚ p) ⇒ (Δ ⊔ Γ ⊢ₚ p) :=
begin
  intro h,
  induction h,
    apply prf.ax,
      apply mem_exg_append_right,
        exact h_h,
    exact prf.pl1 _,
    exact prf.pl2 _,
    exact prf.pl3 _,
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def exg {p q r : form σ} {Γ : ctx σ} :
  (Γ ⸴ p ⸴ q ⊢ₚ r) ⇒ (Γ ⸴ q ⸴ p ⊢ₚ r) :=
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
      exact h_ih_hp
end

def exg_left {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⊢ₚ q) ⇔ ({p} ⊔ Γ ⊢ₚ q) :=
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
      exact prf.pl3 _,
      apply prf.mp,
        exact h_ih_hpq,
        exact h_ih_hp,
    intro h,
    induction h,
      apply prf.ax,
        cases h_h,
         induction h_h,
           apply trivial_mem_right,
           apply mem_ext_cons_left,
             exact h_h,
      exact prf.pl1 _,
      exact prf.pl2 _,
      exact prf.pl3 _,
      apply prf.mp,
        exact h_ih_hpq,
        exact h_ih_hp,
end

/- subcontext operations -/

def subctx_ax {Γ Δ : ctx σ} {p : form σ} :
   Δ ⊆ Γ ⇒ (Δ ⊢ₚ p) ⇒ (Γ ⊢ₚ p) :=
begin
  intros s h,
  induction h,
    apply prf.ax (s h_h),            
    exact prf.pl1 _,
    exact prf.pl2 _,
    exact prf.pl3 _,
    apply prf.mp,
      exact h_ih_hpq,
      exact h_ih_hp
end

def subctx_contr {Γ Δ : ctx σ} {p : form σ}:
   Δ ⊆ Γ ⇒ (Γ ⊔ Δ ⊢ₚ p) ⇒ (Γ ⊢ₚ p) :=
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
      exact h_ih_hp
end


/- right-hand side basic rules of inference -/

def pr {Γ : ctx σ} {p : form σ} :
  Γ ⸴ p ⊢ₚ p :=
by apply ax; apply or.intro_left; simp

def pr1 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⸴ q ⊢ₚ p :=
by apply ax; apply or.intro_right; apply or.intro_left; simp

def pr2 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⸴ q ⊢ₚ q :=
by apply ax; apply or.intro_left; simp

def by_mp1 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⸴ p ⊃ q ⊢ₚ q :=
prf.mp pr2 pr1

def by_mp2 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⊃ q ⸴ p ⊢ₚ q :=
prf.mp pr1 pr2

def cut {Γ : ctx σ} {p q r : form σ} :
  (Γ ⊢ₚ p ⊃ q) ⇒ (Γ ⊢ₚ q ⊃ r) ⇒ (Γ ⊢ₚ p ⊃ r) :=
λ H1 H2, prf.mp (prf.mp (prf.pl2 _) (prf.mp (prf.pl1 _) H2 )) H1

def conv_deduction {Γ : ctx σ} {p q : form σ} :
  (Γ ⊢ₚ p ⊃ q) ⇒ (Γ ⸴ p ⊢ₚ q) :=
λ h, prf.mp (weak h) pr 

/- left-hand side basic rules of inference -/

def mp_in_ctx_left {Γ : ctx σ} {p q r : form σ} :
  (Γ ⸴ p ⸴ q ⊢ₚ r) ⇒ (Γ ⸴ p ⸴ p ⊃ q ⊢ₚ r) :=
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
      exact h_ih_hp
end

def mp_in_ctx_right {Γ : ctx σ} {p q r : form σ} :
  (Γ ⸴ p ⸴ p ⊃ q ⊢ₚ r) ⇒ (Γ ⸴ p ⸴ q ⊢ₚ r) :=
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
      exact h_ih_hp
end

/- basic lemmas -/

def contrap {Γ : ctx σ} {p q : form σ} :
  Γ ⊢ₚ ((~q) ⊃ (~p)) ⊃ (p ⊃ q) :=
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
  Γ ⊢ₚ (~~p) ⊃ p :=
have h : Γ ⊢ₚ (~~p) ⊃ ((~p) ⊃ (~p)) := prf.mp (prf.pl1 _) id,
prf.mp (prf.mp (prf.pl2 Γ) (cut (prf.pl1 Γ) (prf.pl3 Γ))) h

def dni {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₚ p ⊃ (~~p) :=
prf.mp contrap dne 

def lem {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₚ  p ∨ ~p :=
prf.mp dni (prf.mp contrap dne)

def nimpl_to_and {p q : form σ} {Γ : ctx σ} :
  Γ ⊢ₚ (~(p ⊃ q)) ⊃ (p & (~q)) :=
begin
  repeat {apply deduction},
    apply (prf.mp pr1),
      apply deduction,
        apply prf.mp, apply dne,
          exact (prf.mp pr1 pr2),
end

/- notable introduction rules -/

def negintro {p q : form σ} {Γ : ctx σ} :
  (Γ ⊢ₚ p ⊃ q) ⇒ (Γ ⊢ₚ p ⊃ ~q) ⇒ (Γ ⊢ₚ ~p) :=
have h : ∀ q, (Γ ⊢ₚ p ⊃ q) ⇒ (Γ ⊢ₚ (~~p) ⊃ q) := λ q h, cut dne h,
  λ hp hnp, prf.mp (prf.mp (prf.pl3 _) (h (~q) hnp)) (h q hp)

def ex_falso {Γ : ctx σ} {p : form σ} :
  (Γ ⊢ₚ ⊥) ⇒ (Γ ⊢ₚ p) :=
begin
  intro h,
  apply prf.mp,
    exact dne,
    apply prf.mp,
      exact prf.pl1 _,
      exact h
end

def ex_falso_and {Γ : ctx σ} {p q : form σ} :
  Γ ⊢ₚ (~p) ⊃ (p ⊃ q) :=
begin
  repeat {apply deduction},
  apply ex_falso,
  exact (prf.mp pr1 pr2)
end

def impl_weak {p q r : form σ} {Γ : ctx σ} (h : (Γ ⸴ r ⊢ₚ p) ⇒ (Γ ⊢ₚ p)) :
  ((Γ ⊢ₚ p) ⇒ (Γ ⊢ₚ q)) ⇒ ((Γ ⸴ r ⊢ₚ p) ⇒ (Γ ⸴ r ⊢ₚ q)) :=
λ hpq hp, weak (hpq (h hp))

def and_elim_left {p q : form σ} {Γ : ctx σ} :
  (Γ ⸴ (p & q) ⊢ₚ p) :=
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
  (Γ ⸴ (p & q) ⊢ₚ q) :=
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

/- def impl_intro {p q : form} {Γ : ctx} :
  ((Γ ⊢ₚ p) ⇒ (Γ ⊢ₚ q)) ⇒ (Γ ⊢ₚ p ⊃ q) :=
begin
  intro h,
end -/

--def impl_intro {p q : form} {Γ : ctx} :
--  ((Γ ⊢ₚ p) ⇒ (Γ ⊢ₚ q)) ⇒ (Γ ⸴ p ⊢ₚ q) :=
--begin
--  intro h,
--end

end prf
