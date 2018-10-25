/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import ..prime data.encodable .syntax.language.basic

open form nat list decidable 

variables {σ : nat}

/- encoding of propositional formulas -/

@[reducible]
def encode_form : form σ → nat
| (atom v)   := 3^(v.1 + 1)
|  (bot σ)   := 2
| (impl p q) := 5^(encode_form p) * 7^(encode_form q)

/- our encoding is well behaved -/

def is_atom (n : nat) : Prop :=
list.rec_on (factors n) true (λ n _ ih, if n = 3 then ih else false)

def is_impl (n : nat) : Prop :=
list.rec_on (factors n) true (λ n _ ih, if n = 5 ∨ n = 7 then ih else false)

instance is_atom_dec {n : nat} : decidable (is_atom n) :=
begin
  induction n, simp,
    apply is_true, trivial,
    unfold is_atom ite, induction factors (succ n_n),
      simp, apply is_true, trivial,
      simp, induction (nat.decidable_eq hd 3),
        simp, apply is_false, apply id,
        simp, assumption
end

instance is_impl_dec {n : nat} : decidable (is_impl n) :=
begin
  induction n, simp,
    apply is_true, trivial,
    unfold is_impl ite, induction factors (succ n_n),
      simp, apply is_true, trivial,
      simp, induction (nat.decidable_eq hd _),
        repeat {
          induction or.decidable,
            simp, apply is_false, apply id,
            simp, assumption
        }
end

def encode_ge_one : ∀ (p : form σ), encode_form p ≥ 1
| (#v) := by apply nat.le_trans (succ_le_succ (zero_le 1)); apply prime_exp_le prime_three
| (bot σ) := dec_trivial
| (p ⊃ q) := 
  by apply nat.le_trans (succ_le_succ (zero_le 1)); 
  apply prime_double_exp_le prime_five prime_seven
  (encode_ge_one p) (encode_ge_one q)

def is_atom_pow_three : ∀ (n : ℕ), is_atom (3^n)
| 0 := by unfold is_atom ite
| (k+1) := by unfold is_atom ite; rw factors_of_exp_prime prime_three; apply is_atom_pow_three

def not_atom_pow_five_seven  {n m : ℕ } : ¬ is_atom (5^(n+1) * 7^(m+1)) :=
have ¬ 5 = 3 := dec_trivial,
by unfold is_atom ite; rw factors_of_double_exp_prime prime_five prime_seven (le_succ 6);
  simp; induction nat.decidable_eq _ _; simp; contradiction

def min_fac_pow_of_five_seven {i j : ℕ} : min_fac (5^(i+1) * 7^(j+1)) = 5 := 
prime_exp_mul_min_fac_is_least_prime dec_trivial prime_five prime_seven (le_add_left _ _) _ (le_add_left _ _)

def is_impl_pow_of_seven : ∀ {j : ℕ}, is_impl (7^(j+1))
| 0     :=  have h₁ : 7 > 0 := dec_trivial,
            begin
              unfold is_impl ite, rw factors_min_fac (prime_exp_le prime_seven),
              simp, induction nat.decidable_eq _ _,
                induction or.decidable,
                  simp, cases (not_or_iff_and_not _ _).1 h_1,
                    apply false.rec, apply right, exact prime_exp_min_fac_is_self prime_seven,
                  simp, rw [prime_exp_min_fac_is_self prime_seven, nat.pow_one, nat.div_self h₁, factors_one], simp,
                apply absurd h, 
                  rw prime_exp_min_fac_is_self prime_seven, exact dec_trivial
            end

| i@(k+1) :=
  begin
  unfold is_impl ite, rw factors_min_fac (prime_exp_le prime_seven),
    simp, induction nat.decidable_eq _ _,
      induction or.decidable,
        simp, cases (not_or_iff_and_not _ _).1 h_1,
          apply false.rec, apply right, exact prime_exp_min_fac_is_self prime_seven,
        simp, rw [prime_exp_min_fac_is_self prime_seven, mul_exp_div _ (lt_trans (nat.zero_lt_succ _) (prime.ge_two prime_seven))],
        apply is_impl_pow_of_seven,
      apply absurd h,
        rw prime_exp_min_fac_is_self prime_seven, exact dec_trivial
  end

def is_impl_pow_of_five_seven {j : ℕ} : ∀ {i : ℕ}, is_impl (5^(i+1) * 7^(j+1))
| 0     :=  begin
              unfold is_impl ite, rw factors_min_fac (prime_double_exp_le prime_five prime_seven (le_add_left _ _) (le_add_left _ _)),
              simp, induction nat.decidable_eq _ _,
                apply false.rec, apply h, exact min_fac_pow_of_five_seven,
                induction or.decidable,
                  simp, cases (not_or_iff_and_not _ _).1 h_1,
                    apply false.rec, apply left, exact min_fac_pow_of_five_seven,
                  simp, rw min_fac_pow_of_five_seven, rw mul_exp_div_right (prime.ge_two prime_five),
                  rw [nat.pow_zero, mul_comm, nat.mul_one],
                  apply is_impl_pow_of_seven
            end

| i@(k+1) :=
have h₁ : 5 < 7 := dec_trivial,
have h₂ : min_fac (5^(i+1) * 7^(j+1)) = 5 := prime_exp_mul_min_fac_is_least_prime h₁ prime_five prime_seven (le_add_left _ _) _ (le_add_left _ _),
  begin
    unfold is_impl ite, rw factors_min_fac (prime_double_exp_le prime_five prime_seven (le_add_left _ _) (le_add_left _ _)),
    simp, induction nat.decidable_eq _ _,
      contradiction,
      induction or.decidable,
        simp, cases (not_or_iff_and_not _ _).1 h_1,
          contradiction,
        simp, rw h₂, rw mul_exp_div_right (prime.ge_two prime_five),
        apply is_impl_pow_of_five_seven
  end

lemma is_impl_has_pow_of_five_seven : ∀ (n : ℕ), n ≠ 0 → is_impl n → ∃ (i j : ℕ), n = 5^i * 7^j
| 0      := by intro; contradiction 
| 1      := by intros; fapply exists.intro 0; fapply exists.intro 0; repeat {rw nat.pow_zero}; simp
| (k+2)  :=
  have h₁ : (k+2) / min_fac (k+2) < k+2 := factors_lemma,
  have h₂ : (k+2) > 0 := lt_trans (zero_lt_succ 0) (le_add_left _ _),
  begin
    intro h, unfold is_impl ite, rw factors_min_fac (le_add_left _ _),
    simp, induction nat.decidable_eq _ _,
      induction or.decidable,
        simp, simp, intro h₃,
          have hn : ∃ (i j : ℕ), (k + 2) / min_fac (k + 2) = 5 ^ i * 7 ^ j := 
            is_impl_has_pow_of_five_seven ((k+2) / min_fac (k+2)) (pos_div_min_fac (k+2) h₂) h₃,
          cases hn with i h_3,
            cases h_3 with j h_3,
              rw (or.resolve_left h_2 h_1) at h_3,
              fapply exists.intro i, fapply exists.intro (j+1),
                rw [nat.pow_succ, eq.symm (nat.mul_assoc (5^i) (7^j) _), eq.symm h_3],
                apply eq.symm, apply nat.div_mul_cancel,
                  rw eq.symm (or.resolve_left h_2 h_1),
                  apply min_fac_dvd,
      induction or.decidable,
        cases (not_or_iff_and_not _ _).1 h_2,
          contradiction,
        simp, intro h₃, 
            have hn : ∃ (i j : ℕ), (k + 2) / min_fac (k + 2) = 5 ^ i * 7 ^ j :=
              is_impl_has_pow_of_five_seven ((k+2) / min_fac (k+2)) (pos_div_min_fac (k+2) h₂) h₃,
            cases hn with i h_3,
              cases h_3 with j h_3,
              rw h_1 at h_3, 
              fapply exists.intro (i+1), fapply exists.intro j,
                rw [nat.pow_succ, (nat.mul_assoc (5^i) _ (7^j)), nat.mul_comm 5 (7^j)],
                rw [eq.symm (nat.mul_assoc (5^i) (7^j) _), eq.symm h_3],
                apply eq.symm, apply nat.div_mul_cancel,
                  rw eq.symm h_1,
                  apply min_fac_dvd
  end

-- our decoding function is well-founded

lemma impl_five_count_lt (n ≠ 0) : is_impl n → count 5 (factors n) < n :=
have h₁ : 5 < 7 := dec_trivial, 
begin
  intro h₂, cases is_impl_has_pow_of_five_seven n H h₂ with i h₂, cases h₂ with j h₂,
    rw h₂, rw count_exps_factors_right prime_five prime_seven h₁,
    cases nat.decidable_eq i 0,
      cases nat.decidable_eq j 0,
        apply lt_trans,
          apply exp_lt_pow 5 dec_trivial,
            rw nat.mul_comm, apply lt_mul_of_gt_one_left, 
              apply pow_lt_of_self_lt,
                exact dec_trivial, apply pos_iff_ne_zero.2 h_1,
              apply lt_trans (zero_lt_succ 0),
                apply pow_lt_of_self_lt,
                  exact dec_trivial, apply pos_iff_ne_zero.2 h,
        rw h_1, rw nat.pow_zero, rw nat.mul_one,
        apply exp_lt_pow, exact dec_trivial,
      rw h, rw nat.pow_zero, rw nat.mul_comm, rw nat.mul_one,
      apply pow_ge_one, exact dec_trivial
end

lemma impl_seven_count_lt (n ≠ 0) : is_impl n → count 7 (factors n) < n :=
have h₁ : 5 < 7 := dec_trivial, 
begin
  intro h₂, cases is_impl_has_pow_of_five_seven n H h₂ with i h₂, cases h₂ with j h₂,
    rw h₂, rw count_exps_factors_left prime_five prime_seven h₁,
    cases nat.decidable_eq j 0,
      cases nat.decidable_eq i 0,
        apply lt_trans,
          apply exp_lt_pow 7 dec_trivial,
            apply lt_mul_of_gt_one_left,
              apply pow_lt_of_self_lt,
                exact dec_trivial, apply pos_iff_ne_zero.2 h_1,
              apply lt_trans (zero_lt_succ 0),
                apply pow_lt_of_self_lt,
                  exact dec_trivial, apply pos_iff_ne_zero.2 h,
        rw h_1, rw nat.pow_zero, rw nat.mul_comm, rw nat.mul_one,
        apply exp_lt_pow, exact dec_trivial,
      rw h, rw nat.pow_zero, rw nat.mul_one,
      apply pow_ge_one, exact dec_trivial
end

/- decoding of propositional formulas -/

@[reducible]
def decode_form (σ : nat) : nat → option (form σ)
|   0     := none 
|   1     := none 
|   2     := some (bot σ)
| n@(k+3) := 
  if is_atom n 
  then
    if h : count 3 (factors n) - 1 < σ
    then 
      option.some (#⟨count 3 (factors n) - 1,h⟩) 
    else
      none
  else if h : is_impl n 
    then
      have count 5 (factors n) < n := impl_five_count_lt _ (succ_ne_zero _) h,
      have count 7 (factors n) < n := impl_seven_count_lt _ (succ_ne_zero _) h,
      option.rec_on (decode_form (count 5 (factors n))) none
      (λ p, option.rec_on (decode_form (count 7 (factors n))) none 
        (λ q, some (p ⊃ q)) )
    else none 

def decode_form_lemma {n : ℕ} (h : n ≥ 3) :
  decode_form σ n =
    if is_atom n 
    then
      if h₁ : count 3 (factors n) - 1 < σ 
      then 
        option.some (#⟨count 3 (factors n) - 1,h₁⟩) 
      else
        none
    else if h₂ : is_impl n 
      then
        have count 5 (factors n) < n := impl_five_count_lt _ (by intro hn; cases hn; apply absurd h (not_lt_zero 2)) h₂,
        have count 7 (factors n) < n := impl_seven_count_lt _ (by intro hn; cases hn; apply absurd h (not_lt_zero 2)) h₂,
        option.rec_on (decode_form σ (count 5 (factors n))) none
        (λ p, option.rec_on (decode_form σ (count 7 (factors n))) none 
          (λ q, some (p ⊃ q)) )
      else none 
 :=
by cases le.dest h; unfold dite; rw h_1.symm; rw nat.add_comm 3 w at *; unfold decode_form ite dite

/- encoding of propositional formulas preserves data -/

-- falsum

def encodek_bot : decode_form σ (encode_form (⊥ : form σ)) = some ⊥ :=
by unfold decode_form

-- atom

def encodek_atom (v : var σ) : decode_form σ (encode_form (#v)) = some (#v) :=
match v with 
⟨ n , h ⟩  := begin 
                unfold encode_form, induction n, 
                  simp, unfold decode_form ite,
                  rw nat.add_comm 0 3 at *, simp at *,
                    induction is_atom_dec,
                    apply absurd (is_atom_pow_three 1),
                      rw nat.pow_one 3, assumption,
                    simp at *, unfold dite,
                    induction nat.decidable_lt _ _,
                      simp, rw nat.add_zero 3 at *,
                      rw factors_of_prime prime_three at *,
                        simp at *, cases eq_or_lt_of_le h_2,
                          rw h_3 at *, apply absurd h, apply lt_irrefl,
                          apply nat.lt_asymm h, assumption,
                      simp, apply fin.eq_of_veq, unfold fin.val,
                        rw factors_of_prime prime_three, simp,

                  have hle : 3^((succ n_n)+1) ≥ 3 := le_pow_self (succ_le_succ (nat.zero_le 2)),
                  simp, rw decode_form_lemma hle, unfold ite, 
                  induction is_atom_dec,
                    apply absurd (is_atom_pow_three _) h_1,
                    unfold dite, induction nat.decidable_lt _ _,
                      simp, rw factors_of_exp_prime prime_three at *,
                        apply h_2, rw count_cons_self, rw count_exp_factors prime_three,
                        simp, repeat {assumption},
                      simp, apply fin.eq_of_veq, unfold fin.val,
                        rw count_exp_factors prime_three, simp
              end 
end

lemma imp_encode_ge_three {p q : form σ} : 5^(encode_form p) * 7^(encode_form q) ≥ 3 :=
have h₁ : 3 ≤ 5 := dec_trivial,
have h₂ : 1 ≤ 5 := dec_trivial,
have h₃ : 1 ≤ 7 := dec_trivial,
begin
  apply le_trans h₁,
    apply le_trans (pow_le_no_pow h₂ (encode_ge_one p)),
        rw nat.mul_comm, apply le_mul_of_ge_one_left'',
          apply le_trans h₃ (pow_le_no_pow h₃ (encode_ge_one q)),
          apply le_trans (nat.zero_le 5), apply (pow_le_no_pow h₂ (encode_ge_one p))
end

-- implication

def encodek_impl {p q : form σ} :
  decode_form σ (encode_form p) = some p → 
  decode_form σ (encode_form q) = some q →
  decode_form σ (encode_form (p ⊃ q)) = some (p ⊃ q) :=
begin
  intros hp hq, unfold encode_form,
  have hle : 5^(encode_form p) * 7^(encode_form q) ≥ 3 := imp_encode_ge_three,
  rw decode_form_lemma hle, unfold ite, 
  induction is_atom_dec,
    simp, induction is_impl_dec,
      cases le.dest (encode_ge_one p), rw nat.add_comm at h_2,
        cases le.dest (encode_ge_one q), rw nat.add_comm at h_3,
          unfold dite, simp, 
        apply h_1, induction h_2, induction h_3,
          apply is_impl_pow_of_five_seven,
      unfold dite,
        rw count_exps_factors_right prime_five prime_seven,
        rw count_exps_factors_left prime_five prime_seven,
        rw [hp,hq], repeat {apply le_succ},
    apply absurd h, 
      cases le.dest (encode_ge_one p), rw nat.add_comm at h_1,
      cases le.dest (encode_ge_one q), rw nat.add_comm at h_2,
        induction h_1, induction h_2,
          apply not_atom_pow_five_seven
end

-- putting all the pieces together

def encodek_form : ∀ (p : form σ), decode_form σ (encode_form p) = some p
| (atom v)   := encodek_atom v
|  (bot σ)   := encodek_bot
| (impl p q) := encodek_impl (encodek_form p) (encodek_form q)

/- enumeration of all propositional atoms -/

instance of_form : encodable (form σ) :=
⟨ encode_form , decode_form σ , encodek_form ⟩ 

def no_code_is_zero : ∀ p : form σ, encodable.encode p ≥ 1 := λ p, encode_ge_one p 
