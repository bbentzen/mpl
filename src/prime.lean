/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

-- factorization of prime numbers

import .nat data.nat.prime data.list.basic

open nat list decidable 

/- least prime factors and factorization of primes with exponents -/

def factors_zero : factors 0 = nil := dec_trivial

def factors_one : factors 1 = nil := dec_trivial  

def factors_min_fac {n : ℕ} (h : n ≥ 2) : 
  factors n = min_fac n :: factors (n / min_fac n) :=
have h : ∃ k, k + 2 = n := by cases (le.dest h); rw nat.add_comm at h_1; constructor; assumption,
by cases h; induction h_h; unfold factors

def factors_of_prime {n : ℕ} (p_n : prime n) : 
  factors n = [n] := 
by calc
  factors n = min_fac n :: factors (n / min_fac n) : factors_min_fac (prime.ge_two p_n)
  ... = n :: factors (n / n) : by rw (and.elim_right ((prime_def_min_fac).1 p_n))
  ... = n :: factors 1 : by rw nat.div_self (le_trans (succ_le_succ (nat.zero_le _)) (prime.ge_two p_n))
  ... = [n] : by unfold factors

lemma prime_exp_min_fac_not_lt {n m : ℕ} (p_n : prime n) : 
  ¬ min_fac (n^(m+1)) < n :=
begin
   cases (dvd_prime_pow p_n).1 (min_fac_dvd (n^(m+1))) with i h_i,
     cases h_i with h_im h_i,
        cases lt_or_ge 1 i, 
          rw h_i, simp, apply pow_le_no_pow,
            cases (prime_def_min_fac.1 p_n),
              exact le_trans (le_succ _) left,
              apply le_of_lt h,
          cases h,
            revert h_i, rw nat.pow_one n,
              intro, rw h_i, apply nat.lt_irrefl,
            cases h_a,
              have hneq : n^(m+1) ≠ 1 :=
                ne_of_gt ((pow_gt_plus_one n) (and.elim_left (prime_def_min_fac.1 p_n)) m),
              cases (prime_def_min_fac.1 (min_fac_prime hneq)),
                simp at *, apply false.rec, revert left, rw h_i, apply not_succ_le_self,
                repeat {assumption}
end

lemma prime_exp_min_fac_is_self {n m : ℕ} (p_n : prime n) : 
  min_fac (n^(m+1)) = n :=
have h : n^1 ∣ n^(m+1) := pow_dvd_pow n (succ_le_succ (nat.zero_le m)),
begin
  rw nat.pow_one n at *, cases eq_or_lt_of_le 
    (min_fac_le_of_dvd (n^(m+1)) n (and.elim_left (prime_def_min_fac.1 p_n)) h),
      assumption,
      apply absurd h_1, apply prime_exp_min_fac_not_lt p_n
end

def pos_div_min_fac (n > 0) : n / min_fac n ≠ 0 :=
ne_of_gt (div_pos' (min_fac_le H) (min_fac_pos _))

lemma prime_exp_le {n m : ℕ} (p_n : prime n) : 
  n^(m+1) ≥ 2 :=
le_trans (prime.ge_two p_n)
(le_trans (le_of_eq (eq.symm (nat.pow_one n)) )
  (pow_le_pow_of_le_right
    (le_trans (succ_le_succ (nat.zero_le _)) (prime.ge_two p_n))
    (succ_le_succ (nat.zero_le (m))) ) )

def factors_of_exp_prime {n m : ℕ} (p_n : prime n) : 
  factors (n^(m+1)) = n :: factors (n^m) := 
by calc
  factors (n^(m+1)) = min_fac ((n^(m+1))) :: factors ((n^(m+1)) / min_fac _) : factors_min_fac (prime_exp_le p_n)
  ... = n :: factors (n^(m+1) / n) : by rw prime_exp_min_fac_is_self p_n 
  ... = n :: factors (n^m) : by rw mul_exp_div _ (lt_trans (nat.zero_lt_succ _) (and.elim_left (prime_def_min_fac.1 p_n))) 

/-- fundamental facts about prime numbers --/

lemma prime_five : prime 5 := sorry --why dec_trivial is not working?

lemma prime_seven : prime 7 := sorry

lemma prime_dvd_exp {n : ℕ} (p_n : prime n) (m > 0) : 
  n ∣ n^m :=
have hm : ∃ i, m = i + 1 := by cases le.dest H; rw nat.add_comm at h; exact ⟨ w, eq.symm h ⟩,
have h : min_fac (n^m) ∣ n^m := min_fac_dvd _,
by cases hm; rw hm_h at *; rw prime_exp_min_fac_is_self p_n at h; exact h

lemma prime_dvd_exp_left {n m j : ℕ} (p_n : prime n) (i > 0) : 
  n ∣ n^i * m^j :=
(prime.dvd_mul p_n).2 (or.inl (prime_dvd_exp p_n _ H))

lemma prime_dvd_exp_right {n m i : ℕ} (p_m : prime m) (j > 0) : 
  m ∣ n^i * m^j :=
(prime.dvd_mul p_m).2 (or.inr (prime_dvd_exp p_m _ H))

lemma prime_double_exp_le {n m i j : ℕ} (p_n : prime n) (p_m : prime m) (h₁ : i > 0) (h₂ : j > 0) :
  n^i*m^j ≥ 2 :=
begin
  cases le.dest h₂, 
    rw add_comm at h, rw eq.symm h,
    apply le_trans,
      apply prime_exp_le p_m, 
        exact w,
      apply le_of_lt, 
        apply lt_mul_of_gt_one_left,
          cases le.dest h₁, rw add_comm at h_1, rw eq.symm h_1,
            apply pow_gt_plus_one, assumption,
            exact prime.ge_two p_n,
            apply nat.le_trans,
              apply nat.le_trans, 
                apply le_succ,
                exact prime.ge_two p_m,
              apply pow_le_no_pow,
                apply nat.le_trans, 
                  apply le_succ,
                  exact prime.ge_two p_m,
                apply le_add_left
end

/-- more about least prime factors and factorization --/

lemma prime_exp_mul_min_fac {n m i j : ℕ} (p_n : prime n) (p_m : prime m) (h₁ : i > 0) (h₂ : j > 0) : 
  min_fac (n^i*m^j) = n ∨ min_fac (n^i*m^j) = m :=
have h : n^i*m^j ≠ 1 := ne_of_gt (prime_double_exp_le p_n p_m h₁ h₂),
begin
  cases (prime.dvd_mul (min_fac_prime _ )).1 (min_fac_dvd ((n^i)*(m^j))),
    left, apply (dvd_prime_ge_two _ _).1,
      apply prime.dvd_of_dvd_pow,
        apply min_fac_prime,
        repeat {assumption},
        cases (prime_def_min_fac.1 (min_fac_prime h)),
          assumption,
    right, apply (dvd_prime_ge_two _ _).1,
      apply prime.dvd_of_dvd_pow,
        apply min_fac_prime,
        repeat {assumption},
        cases (prime_def_min_fac.1 (min_fac_prime h)),
          assumption,
end

lemma prime_exp_mul_min_fac_is_least_prime {n m i : ℕ} (hn : n < m) (p_n : prime n) (p_m : prime m) (h : i > 0) (j > 0) : 
  min_fac (n^i*m^j) = n :=
have hmin : min_fac (n^i*m^j) ≤ n := min_fac_le_of_dvd _ _ (prime.ge_two p_n) (prime_dvd_exp_left p_n _ h) , 
match prime_exp_mul_min_fac p_n p_m h H with
  | or.inl h := h
  | or.inr h := or.elim (eq_or_lt_of_le hmin) id
      (by rw h; intro; apply absurd hn; apply nat.lt_asymm a)
end

def factors_of_double_exp_prime {n m i j : ℕ} (p_n : prime n) (p_m : prime m) (h : n < m) : 
  factors (n^(i+1) * m^j) = n :: factors (n^i * m^j) :=
begin
  cases nat.decidable_le j 0,
    cases lt_or_ge 0 j,
      cases le.dest h_2 with k, rw nat.add_comm at h_3, rw eq.symm h_3,
        calc
          factors (n^(i+1) * m^(k+1)) = min_fac (n^(i+1) * m^(k+1)) :: factors (n^(i+1) * m^(k+1) / min_fac _) : factors_min_fac (prime_double_exp_le p_n p_m (nat.le_add_left _ _) (nat.le_add_left _ _))
          ... = n :: factors ((n^(i+1) * m^(k+1)) / n) : by rw prime_exp_mul_min_fac_is_least_prime h p_n p_m (nat.le_add_left _ _) _ (nat.le_add_left _ _)
          ... = n :: factors (n^i * m^(k+1)) : by rw mul_exp_div_right (prime.ge_two p_n),
      contradiction,
    cases h_1, rw nat.pow_zero, simp,
      exact factors_of_exp_prime p_n
end

/-- enumeration of factors of prime numbers with exponents --/

def count_exp_factors {n m : nat} (p_n : prime n) : 
  count n (factors (n^m)) = m :=
begin
  induction m, 
    simp, unfold factors count countp ite,
    rw factors_of_exp_prime p_n, unfold factors count countp ite,
      induction nat.decidable_eq n n,
        contradiction,
        simp, assumption
end

def count_exp_factors_zero {n m i : nat} (p_n : prime n) (h : m ≠ n) : 
  count m (factors (n^i)) = 0 :=
begin
  induction i, 
    simp, unfold factors count countp ite,
    rw factors_of_exp_prime p_n, unfold factors count countp ite,
      induction nat.decidable_eq _ n,
        simp, assumption,
        contradiction
end

def count_exps_factors_right {n m i j : nat} (p_n : prime n) (p_m : prime m) (h : n < m) : 
  count n (factors (n^i * m^j)) = i :=
begin
  induction i, 
    simp, apply count_exp_factors_zero p_m (ne.symm (ne_of_gt h)),
    rw factors_of_double_exp_prime p_n p_m h, unfold factors count countp ite,
      induction nat.decidable_eq n n,
        contradiction,
        simp, assumption
end

def count_exps_factors_left {n m i j : nat} (p_n : prime n) (p_m : prime m) (h : n < m) : 
  count m (factors (n^i * m^j)) = j :=
begin
  induction i, 
    simp, apply count_exp_factors p_m,
    rw factors_of_double_exp_prime p_n p_m h, unfold factors count countp ite,
      induction nat.decidable_eq m n,
        simp, assumption,
        apply absurd h, apply nat.lt_asymm, induction h_1, assumption
end

def count_factors_le (m : nat) : ∀ n, count m (factors n) ≤ n
| 0 := by unfold factors count countp
| 1 := by unfold factors count countp; apply nat.zero_le
| n@(k+2) :=
  let i := min_fac n in have n / i < n := factors_lemma,
  have h_le : count m (factors ((k + 2)/ i )) ≤ (k + 2) / i := count_factors_le _,
  begin
    unfold factors count countp ite,
    induction (nat.decidable_eq _ _),
      simp, apply le_trans,
        apply count_factors_le, apply nat.div_le_self,
      simp, apply le_trans, apply succ_le_succ, assumption, assumption
  end
