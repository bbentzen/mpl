/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic ..language.basic ..language.lemmas

variable {σ : nat}

/- context membership operations -/

def trivial_mem_left {Γ : ctx σ} {p : form σ} :
  p ∈ (Γ ⸴ p) :=
by apply or.intro_left; apply rfl

def trivial_mem_right {Γ : ctx σ} {p : form σ} :
  p ∈ ({p} ⊔ Γ) :=
by apply or.intro_left; apply rfl

def mem_ext_cons_left {Γ : ctx σ} {p q : form σ} :
  p ∈ Γ → p ∈ (Γ ⸴ q) :=
by intro h; apply or.intro_right; exact h

def mem_ext_cons_left_cp {Γ : ctx σ} {p q : form σ} :
  p ∉ (Γ ⸴ q) → p ∉ Γ :=
by intros hngq hng; apply hngq; apply mem_ext_cons_left; exact hng

def mem_ext_cons_right {Γ : ctx σ} {p q : form σ} :
  p ∈ Γ → p ∈ ({q} ⊔ Γ) :=
by intro h; apply or.intro_right; exact h

def mem_ext_append_left {Γ Δ : ctx σ} {p : form σ} :
  p ∈ Γ → p ∈ (Γ ⊔ Δ) :=
by apply list.mem_append_left

def mem_ext_append_right {Γ Δ : ctx σ} {p : form σ} :
  p ∈ Δ → p ∈ (Γ ⊔ Δ) :=
by apply list.mem_append_right

def mem_contr_cons_right {Γ : ctx σ} {p q : form σ} :
  p ∈ (Γ ⸴ q ⸴ q) → p ∈ (Γ ⸴ q) :=
begin
  intro h,
  cases h,
    induction h,
      apply trivial_mem_left,
      exact h
end

def mem_contr_append_right {Γ Δ : ctx σ} {p : form σ} :
  p ∈ (Γ ⊔ Δ ⊔ Δ) → p ∈ (Γ ⊔ Δ) :=
begin
  intro h,
  cases (list.mem_append.1 h),
    exact h_1,
    apply mem_ext_append_right,
      exact h_1
end

def mem_exg_cons_right {Γ : ctx σ} {p q r : form σ} :
  p ∈ (Γ ⸴ q ⸴ r) → p ∈ (Γ ⸴ r ⸴ q) :=
begin
  intro h,
  cases h,
    induction h,
      apply mem_ext_cons_left,
        apply trivial_mem_left,
        cases h,
          induction h,
            apply trivial_mem_left,
          apply mem_ext_cons_left,
            apply mem_ext_cons_left,
              exact h
end

def mem_exg_append_right {Γ Δ : ctx σ} {p : form σ} :
  p ∈ (Γ ⊔ Δ) → p ∈ (Δ ⊔ Γ) :=
begin
  intro h,
  cases (list.mem_append.1 h),
    apply mem_ext_append_right,
      exact h_1,
    apply mem_ext_append_left,
      exact h_1,
end

def mem_exg_three_append_right {Γ Δ Δ' : ctx σ} {p : form σ} :
  p ∈ (Γ ⊔ Δ ⊔ Δ') → p ∈ (Γ ⊔ Δ' ⊔ Δ) :=
begin
  intro h,
  cases (list.mem_append.1 h),
    cases (list.mem_append.1 h_1),
      apply mem_ext_append_left,
        apply mem_ext_append_left,
          exact h_2,
      apply mem_ext_append_right,
        exact h_2,
    apply mem_ext_append_left,
      apply mem_ext_append_right,
        exact h_1
end

/- subcontext operations -/

def sub_cons_left {Γ Δ : ctx σ} {p : form σ} :
  (Δ ⊆ Γ) → (Δ ⸴ p) ⊆ (Γ ⸴ p) :=
begin
 intros s q qmem, cases qmem, 
   induction qmem, apply trivial_mem_left,
   apply mem_ext_cons_left (s qmem), 
end

def sub_cons_is_sub {Γ Δ : ctx σ} {p : form σ} :
  (Δ ⸴ p) ⊆ Γ → Δ ⊆ Γ :=
by intros s q qmem; apply s; apply mem_ext_cons_left qmem
