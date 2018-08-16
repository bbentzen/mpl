/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

-- Elementary facts about Kripe models without any requirements (K) --/

import .basic ..default

open classical

/- Modal logical constants (=>) -/

def forall_wrld_tt_nec_tt {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p : form} : 
  (∀ v, (v ∈ M.fst.fst) → (M.fst.snd w v) → (M⦃p⦄v)) ⇒ (M⦃◻p⦄w) := 
id

def exists_wlrd_tt_pos_tt {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p : form} : 
  (∃ v, (v ∈ M.fst.fst) ∧ (M.fst.snd w v) ∧ (M⦃p⦄v)) ⇒ (M⦃◇p⦄w) := 
begin
  intros h hn,
  cases h with v h,
    cases h with h1 h2,
      cases h2 with h2 h3,
        exact (hn v h1 h2) h3
end

-- 

/- Modal logical constants (<=) -/

def nec_tt_forall_wrld_tt {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p : form} : 
  (M⦃◻p⦄w) ⇒ (∀ v, (v ∈ M.fst.fst) → (M.fst.snd w v) → (M⦃p⦄v)) := 
id

def pos_tt_exists_wlrd_tt {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p : form} : 
  (M⦃◇p⦄w) ⇒ (∃ v, (v ∈ M.fst.fst) → (M.fst.snd w v) → (M⦃p⦄v)) := 
begin
  intros hpos,
  apply by_contradiction,
    intro hn,
    exact (absurd 
    begin 
      intros v inw r h, 
      exact (absurd 
        begin 
          apply exists.intro,
            intros a b,
            exact h 
        end 
      hn) 
    end 
    hpos)
end

def pos_ff_forall_wrld_ff {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p : form} : 
  ¬(M⦃◇p⦄w) ⇒ (∀ v, (v ∈ M.fst.fst) → (M.fst.snd w v) → ¬(M⦃p⦄v)) := 
begin
  unfold true_in_wrld, 
  apply or.elim (em _),
    intros H1 H2, apply H1,
    intros H1 H2, exact (absurd H1 H2)
end

/- Some facts about K -/

def nec_impl_to_nec_impl_nec {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
  (M⦃◻(p ⊃ q)⦄w) → (M⦃◻p⦄w) → (M⦃◻q⦄w) := 
by intros hnec hp v inw r; exact ((hnec v inw r) (hp v inw r))

def nec_impl_ff_exist_wlrd_ff {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
  ¬ (M⦃◻(p ⊃ q)⦄ w) ⇒ (∃ v, ¬(M⦃p ⊃ q⦄v)) := 
begin
  unfold true_in_wrld,
  intro h,
  apply by_contradiction,
    intro hn,
  have h' : ¬∀ (v : ℕ), (M⦃p⦄v) → (M⦃q⦄v) := 
    begin
      apply not_forall_strgh,
        exact (λ v, v ∈ (M.fst).fst),
        apply not_forall_strgh,
          exact (λ v, M.fst.snd w v),
          exact h 
    end,
    apply absurd,
      exact (forall_not_of_not_exists hn),
      intro hn',
        have hn' : ∀ (v : ℕ), (M⦃p⦄v) → (M⦃q⦄v) := 
          begin
            intros v,
            apply or.elim (em ((M⦃p⦄v) → (M⦃q⦄v))),
              exact id,
              intro nn, exact (absurd nn (hn' v))
          end,
     exact (absurd hn' h') 
end

def nec_nec_to_nec_impl {M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)} {w : nat} {p q : form} : 
  (M⦃◻p⦄w) → (M⦃◻q⦄w) →  (M⦃◻(p ⊃ q)⦄w)  := 
begin
  unfold true_in_wrld,
  intros hp hq v inw r ptt,
  exact (hq v inw r)
end
