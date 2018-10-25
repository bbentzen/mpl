/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

-- basic lemmas about natural numbers and exponentiation

import data.nat.basic

open nat 

lemma lt_mul_of_gt_one_left {n m: ℕ} (h₁ : n > 1) (h₂ : m > 0) : n * m > m :=
have h : n * m > 1 * m := mul_lt_mul h₁ (le_refl m) h₂ (nat.le_trans (zero_le 2) h₁),
by simp at *; exact h

lemma le_mul_of_ge_one_left'' {n m: ℕ} (h₁ : n ≥ 1) (h₂ : m ≥ 0) : n * m ≥ m :=
have h : n * m ≥ 1 * m := mul_le_mul h₁ (le_refl m) h₂ (zero_le n),
by simp at *; exact h

def le_add_le_of_le_add {m n j k : ℕ} (hm : n ≤ m) (hk : j ≤ k) : n + j ≤ m + k := 
le_trans (add_le_add_right hm _) (add_le_add_left hk _)

def lt_add_lt_of_lt_add {m n j k : ℕ} (hm : n < m) (hk : j < k) : n + j < m + k := 
lt_trans (add_lt_add_right hm _) (add_lt_add_left hk _)

def lt_of_lt_add_right (m > 0) : ∀ (n : ℕ), n < n + m
| 0     := by simp; assumption 
| (k+1) := by rw nat.add_assoc; apply add_lt_add_left; rw nat.add_comm; apply succ_lt_succ; exact H

lemma lt_mul_of_gt_one_left_plus_one' {m n : ℕ} (h₁ : m > 1) (h₂ : m > n) : ∀ {k : ℕ}, m * (k+2) > n + 1
| 0:= by simp; rw nat.mul_succ; rw nat.mul_one; apply lt_add_lt_of_lt_add h₂ h₁ 
| (k+1) := 
  begin 
    rw [nat.mul_succ, nat.add_succ, nat.add_zero],
    apply lt_trans, apply lt_mul_of_gt_one_left_plus_one', exact k, 
      apply lt_of_lt_add_right, apply lt_trans,
        exact zero_lt_succ 0, exact h₁    
end

lemma lt_mul_of_gt_one_left_plus_one (m > 1) (n < m) (k > 1) : m * k > n + 1 :=
begin
  cases le.dest H,
    rw nat.add_comm at h, rw eq.symm h,
    apply lt_mul_of_gt_one_left_plus_one', repeat {assumption}
end

/-- ordering and strict ordering of exponential numbers --/

lemma pow_le_no_pow {n i : ℕ} (h₁ : n ≥ 1) (h₂ : i ≥ 1) : n ≤ n^i :=
have n^1 ≤ n^i := pow_le_pow_of_le_right h₁ h₂,
by rw nat.pow_one at *; assumption

lemma le_pow_self {n m : ℕ} (h : n > 0) : n ≤ n^(m+1) :=
have le : n^1 ≤ n^(m+1) := pow_le_pow_of_le_right h (le_add_left 1 m),
by rw nat.pow_one n at *; exact le

lemma gt_pow_self {m n : ℕ} (hn : n > 1) (hm : m > 0) : n^(m+1) > n :=
have n^(m+1) > n^1 := pow_lt_pow_of_lt_right hn (lt_add_of_pos_left 1 hm),
by rw nat.pow_one at *; assumption

lemma pow_gt_plus_one {n : ℕ} (n > 1) : ∀ m, n^(m+1) > 1
|   0   := by simp; assumption
| (m+1) := 
  begin
    apply lt_trans, apply pow_gt_plus_one m, 
    apply pow_lt_pow_of_lt_right, assumption, apply lt.base
  end

def pow_ge_one (n > 0) : ∀ {i : ℕ}, n^i ≥ 1
|   0     := by simp; exact zero_lt_succ 0
| n@(k+1) := 
  begin
    rw nat.pow_succ, rw nat.mul_comm,
    apply le_trans pow_ge_one, apply le_mul_of_ge_one_left'', assumption, apply nat.zero_le
  end

def pow_lt_of_self_lt' (n > 1) : ∀ {i : ℕ}, n^(i+1) > 1
|   0     := by rw nat.pow_one; exact H
| n@(k+1) := 
  begin
    rw nat.pow_succ, rw nat.mul_comm,
    apply lt_mul_of_gt_one_left_plus_one, assumption,
      apply lt_trans, exact zero_lt_succ 0, assumption,
      apply pow_lt_of_self_lt'
  end

def pow_lt_of_self_lt (n > 1) (i > 0) : n^i > 1 :=
begin
  cases le.dest H, rw nat.add_comm at h, rw eq.symm h,
  apply pow_lt_of_self_lt', assumption
end

def exp_lt_pow (n > 1) : ∀ (i : ℕ), i < n^i 
|   0     := by rw nat.pow_zero; exact zero_lt_succ 0  
|   1     := by rw nat.pow_one; exact H
| n@(k+2) := 
  begin
    rw nat.pow_succ, apply lt_mul_of_gt_one_left_plus_one,
      apply pow_lt_of_self_lt', assumption,
      apply exp_lt_pow,
      assumption
  end

lemma div_pos' {a b : ℕ} (hba : b ≤ a) (hb : 0 < b) : 0 < a / b := -- from mathlib (the internal version of div_pos is not working)
nat.pos_of_ne_zero (λ h, lt_irrefl a
  (calc a = a % b : by simpa [h] using (mod_add_div a b).symm
      ... < b : nat.mod_lt a hb
      ... ≤ a : hba))

/-- basic rules for exponentiation simplification --/

def mul_exp_div (n > 0) {m : ℕ } : n^(m+1) / n = (n^m) := 
nat.div_eq_of_eq_mul_left H (nat.pow_succ _ _)

def mul_exp_div_right {n m i : ℕ} (hn : n > 1) :
  n^(i+1) * m / n = (n^i) * m := 
begin
  revert m, induction i, simp,
    intros, apply nat.div_eq_of_eq_mul_left,
      apply lt_trans, 
        apply (nat.zero_lt_succ 0),
          assumption,
          apply nat.mul_comm,
    intros, rw nat.pow_succ n,
      rw mul_assoc _ n m, rw nat.pow_succ n,
      rw mul_assoc _ n m,
      rw eq.symm (nat.pow_succ n _),
      apply i_ih,
end