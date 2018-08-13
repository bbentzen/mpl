/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen

Elementary facts about Kripe models without any requirements (K)
-/

import .basic

/- Non-modal logical constants (=>) -/

def impl_tt_to_impl {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
   ((M⦃p⦄w) = tt → (M⦃q⦄w) = tt) → ((M⦃p ⊃ q⦄w) = tt) := 
by unfold true_in_wrld; induction (true_in_wrld M p w); 
  repeat {induction (true_in_wrld M q w), simp, simp,}

def ff_or_tt_to_impl {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
   ((M⦃p⦄w) = ff ∨ (M⦃q⦄w) = tt) → ((M⦃p ⊃ q⦄w) = tt) := 
by unfold true_in_wrld; induction (true_in_wrld M p w); 
  repeat {induction (true_in_wrld M q w), simp, simp,}

def ff_to_neg {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p : form} : 
   ((M⦃p⦄w) = ff)  → ((M⦃~p⦄w) = tt) := 
by unfold true_in_wrld; induction (true_in_wrld M p w); simp; apply eq.symm

def tt_tt_to_and {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
   ((M⦃p⦄w) = tt) → ((M⦃q⦄w) = tt) → ((M⦃(p & q)⦄w) = tt) := 
by unfold true_in_wrld; induction (true_in_wrld M p w); 
  repeat {induction (true_in_wrld M q w), simp, simp,}

def tt_to_or_left {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
   ((M⦃p⦄w) = tt) → ((M⦃(p ∨ q)⦄w) = tt) := 
by unfold true_in_wrld; induction (true_in_wrld M p w); 
  repeat {induction (true_in_wrld M q w), simp, simp,}

def tt_to_or_right {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
   ((M⦃q⦄w) = tt) → ((M⦃(p ∨ q)⦄w) = tt) := 
by unfold true_in_wrld; induction (true_in_wrld M p w); 
  repeat {induction (true_in_wrld M q w), simp, simp,}

/- Non-modal logical constants (<=) -/

def impl_to_tt_tt {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
   ((M⦃(p ⊃ q)⦄w) = tt) → ((M⦃p⦄w) = tt) → ((M⦃q⦄w) = tt)  := 
by unfold true_in_wrld; induction (true_in_wrld M p w); 
  repeat {induction (true_in_wrld M q w), simp, simp,}

def neg_to_efq {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
   ((M⦃~p⦄w) = tt) → ((M⦃p⦄w) = tt) → ((M⦃q⦄w) = tt)  := 
by unfold true_in_wrld; induction (true_in_wrld M p w); 
  repeat {induction (true_in_wrld M q w), simp, simp,}

def and_to_tt_tt {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
   ((M⦃(p & q)⦄w) = tt) → ((M⦃p⦄w) = tt) → ((M⦃q⦄w) = tt)  := 
by unfold true_in_wrld; induction (true_in_wrld M p w); 
  repeat {induction (true_in_wrld M q w), simp, simp,}

/- Modal logical constants (=>) -/

def nec_ff_exists_wrld_ff {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p : form} : 
  ((M⦃◻p⦄w) = ff) ⇒ (∃ v, ((M.fst.snd w v) = tt) ∧ ((M⦃p⦄v) = ff)) := 
begin
  unfold true_in_wrld,
  induction M.fst.fst with v IH,
    simp, simp,
    intro H,
    cases H with H1 H2,
     exact (IH H1),
     exact ⟨v, H2⟩ 
end

def all_wrlds_tt_nec_tt {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p : form} : 
(∀ v, ((M.fst.snd w v = tt) → (M⦃p⦄v) = tt)) ⇒ ((M⦃◻p⦄w) = tt)  := 
begin
  intro f,
  apply eq_tt_of_not_eq_ff,
  apply 
    (show ¬ (∃ v, (_ = tt) ∧ (_ = ff)) ⇒ ¬ (_ = ff) , 
      from λ f a, f (nec_ff_exists_wrld_ff a) ),
    intro g, 
    cases g with v h,
      cases h with h1 h2,
        exact (bool.no_confusion (eq.trans (eq.symm (f v h1)) h2))
end

/- Some facts about K  -/

def nec_impl_to_nec_nec {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
  ((M⦃◻(p ⊃ q)⦄w) = tt) → (M⦃◻p⦄w) = tt → (M⦃◻q⦄w) = tt := 
begin
  unfold true_in_wrld,
  induction M.fst.fst with k IH,
    simp, simp at *,
      intros Hpq Hp,
        cases Hpq with Hpq1 Hpq2,
          cases Hp with Hp1 Hp2,
            apply and.intro,
              exact (IH Hpq1 Hp1),
              cases Hpq2,
                apply or.intro_left,
                  assumption, 
                cases Hp2,
                  apply or.intro_left,
                    assumption,
                  cases Hpq2,
                    exact (bool.no_confusion (eq.trans (eq.symm Hp2) Hpq2)),
                    apply or.intro_right,
                      assumption
end

definition nec_impl_ff_exist_wlrd_ff {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
  ((M⦃◻(p ⊃ q)⦄ w) = ff) ⇒ (∃ k : nat, ((M⦃p⦄k) = tt) ∧ ((M⦃q⦄k) = ff)) := 
begin
  unfold true_in_wrld,
  induction M.fst.fst with k IH,
    simp, simp,
    intro H,
    cases H with H1 H2,
      exact (IH H1),
      cases H2,
      exact ⟨k, H2_right⟩
end

def nec_nec_to_nec_impl_nec {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
  ((M⦃◻p⦄w) = tt) → ((M⦃◻q⦄w) = tt) → ((M⦃(◻p) ⊃ (◻q)⦄w) = tt) := 
begin
  unfold true_in_wrld,
  induction M.fst.fst with v IH,
    intros H1 H2,
    simp, simp,
    intros H1 H2,
    apply or.intro_right,
      assumption
end

def nec_impl_to_nec_impl_nec {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
  ((M⦃◻(p ⊃ q)⦄w) = tt) → ((M⦃◻p⦄w) = tt → (M⦃◻q⦄w) = tt) := 
begin
  unfold true_in_wrld,
  induction M.fst.fst with k IH,
    simp, simp,
    intros H1 H2,
      cases H1,
        cases H2,
          apply and.intro,
            exact (IH H1_left H2_left),
            cases H1_right,
              apply or.intro_left,
                assumption,
                cases H1_right,
                  cases H2_right,
                    apply or.intro_left,
                      assumption,
                      exact (bool.no_confusion 
                        (eq.trans (eq.symm H2_right) H1_right)),
                    apply or.intro_right,
                      assumption
end 


/-

def pos_ff_exists_wrld_ff {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p : form} : 
  ((M⦃◇p⦄w) = ff) ⇒ (∀ v, ((M.fst.snd w v) = tt) → ((M⦃p⦄v) = tt)) := 
begin
  unfold true_in_wrld,
  induction M.fst.fst with v IH,
  simp, intros v H,sorry,
    simp,
end

-/
