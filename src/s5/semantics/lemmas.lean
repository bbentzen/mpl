/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic

open form classical

variable {σ : nat}

/- general facts about non-modal logical constants -/

lemma neg_tt_iff_ff {M : model} {w : wrld σ} {p : form σ} :
  (w ⊩⦃M⦄ ~p) = tt ↔ ¬(w ⊩⦃M⦄ p) :=
by unfold forces_form; induction (forces_form M p w); simp; simp

lemma neg_ff_iff_tt {M : model} {w : wrld σ} {p : form σ} :
  ¬(w ⊩⦃M⦄ ~p) ↔ (w ⊩⦃M⦄ p) = tt :=
by unfold forces_form; induction (forces_form M p w); simp; simp

lemma impl_iff_implies {M : model} {w : wrld σ} {p q : form σ} :
  (w ⊩⦃M⦄ p ⊃ q) = tt ↔ ((w ⊩⦃M⦄ p) → (w ⊩⦃M⦄ q)) :=
by unfold forces_form; induction (forces_form M p w); repeat {induction (forces_form M q w), simp, simp}

lemma impl_tt_iff_ff_or_tt {M : model} {w : wrld σ} {p q : form σ} :
  (w ⊩⦃M⦄ p ⊃ q) = tt ↔ ¬(w ⊩⦃M⦄ p) ∨ (w ⊩⦃M⦄ q) = tt :=
by unfold forces_form; induction (forces_form M p w); repeat {induction (forces_form M q w), simp, simp}

lemma ff_or_tt_and_tt_implies_tt_right {M : model} {w : wrld σ} {p q : form σ} :
  (¬(w ⊩⦃M⦄ p) ∨ (w ⊩⦃M⦄ q) = tt) → (w ⊩⦃M⦄ p) = tt → (w ⊩⦃M⦄ q) = tt :=
by simp; induction (forces_form M p w); repeat {induction (forces_form M q w), simp, simp}

lemma bot_is_insatisf {w : wrld σ} : 
  ¬ ∃ (M : model), (w ⊩⦃M⦄ bot σ) = tt :=
by intro h; cases h; exact (bool.no_confusion h_h) 

/- Modal logical constants (=>) -/

lemma forall_wrld_tt_nec_tt {M : model} {w : wrld σ} {p : form σ} : 
  (∀ v ∈ M.wrlds, w ∈ M.wrlds → M.access w v → (v ⊩⦃M⦄ p) = tt) → (w ⊩⦃M⦄ ◻p) = tt := 
begin
  intro h, 
  unfold forces_form,
  induction (prop_decidable _),
  { simp, contradiction },
  { simp, assumption }
end

lemma exists_wlrd_tt_pos_tt {M : model} {w : wrld σ} {p : form σ} : 
  (∃ v ∈ M.wrlds, w ∈ M.wrlds ∧ M.access w v = tt ∧ (v ⊩⦃M⦄ p) = tt) → (w ⊩⦃M⦄ ◇p) = tt := 
begin
  intro h,
  unfold forces_form,
  induction (prop_decidable _),
  { simp, intro hf, cases h, cases h_h, cases h_h_h, cases h_h_h_right,
    apply tt_eq_ff_eq_false,
    rw eq.symm h_h_h_right_right, 
    apply hf, repeat {assumption} },
  { simp, intro hf, cases h, cases h_h, cases h_h_h, cases h_h_h_right,
    apply bot_is_insatisf, apply exists.intro, apply impl_iff_implies.1,
    apply h_1, repeat {assumption} }
end

/- Modal logical constants (<=) -/

lemma nec_tt_forall_wrld_tt {M : model} {w : wrld σ} {p : form σ} : 
  (w ⊩⦃M⦄ ◻p) = tt → (∀ v ∈ M.wrlds, w ∈ M.wrlds → M.access w v = tt → (v ⊩⦃M⦄ p) = tt) := 
begin
  unfold forces_form,
  induction (prop_decidable _),
  repeat {simp}
end

lemma pos_tt_exists_wlrd_tt {M : model} {w : wrld σ} {p : form σ} : 
  (w ⊩⦃M⦄ ◇p) = tt → (∃ v ∈ M.wrlds, w ∈ M.wrlds ∧ M.access w v = tt ∧ (v ⊩⦃M⦄ p) = tt) := 
begin
  unfold forces_form,
  simp, intro h,
  apply classical.by_contradiction, intro h',
  have nh : ∀ v ∈ M.wrlds, w ∈ M.wrlds → M.access w v = tt → (v ⊩⦃M⦄ p) ≠ tt :=
    begin
      intros v wmem vmem rwv ptt, apply h',
      repeat {split},
      assumption, 
      exact vmem,
      repeat {assumption}
    end,
  apply h, intros v wmem vmem rwv,
  apply eq_ff_of_not_eq_tt,
  apply nh, repeat {assumption}
end

lemma pos_ff_forall_wrld_ff {M : model} {w : wrld σ} {p : form σ} : 
  ¬(w ⊩⦃M⦄ ◇p) → (∀ v ∈ M.wrlds, w ∈ M.wrlds → M.access w v = tt → ¬(v ⊩⦃M⦄ p)) := 
by unfold forces_form; simp; exact id

/- Some facts about PL -/

lemma is_true_pl1 {M : model} {w : wrld σ} {p q : form σ} : 
  (w ⊩⦃M⦄ p ⊃ (q ⊃ p)) = tt := 
begin
  apply impl_iff_implies.2,
  intro, apply impl_iff_implies.2,
  intro, assumption
end

lemma is_true_pl2 {M : model} {w : wrld σ} {p q r : form σ} : 
  (w ⊩⦃M⦄ (p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r))) = tt := 
begin
  apply impl_iff_implies.2,
  intro h₁, apply impl_iff_implies.2,
  intro h₂, apply impl_iff_implies.2,
  intro h₃, apply impl_iff_implies.1 ((impl_iff_implies.1 h₁) h₃),
  apply impl_iff_implies.1 h₂, assumption
end

lemma is_true_pl3 {M : model} {w : wrld σ} {p q : form σ} : 
  (w ⊩⦃M⦄ ((~p) ⊃ ~q) ⊃ (((~p) ⊃ q) ⊃ p)) = tt := 
begin
  unfold forces_form,
  induction (forces_form M p w),
  repeat { induction (forces_form M q w), repeat {simp} },
end

/- Some facts about K -/

lemma nec_impl_to_nec_to_nec {M : model} {w : wrld σ} {p q : form σ} : 
  (w ⊩⦃M⦄ ◻(p ⊃ q)) = tt → (w ⊩⦃M⦄ ◻p) = tt → (w ⊩⦃M⦄ ◻q) = tt := 
begin
  unfold forces_form, simp at *, intros hlpq hlp v wmem vmem rwv,
  apply ff_or_tt_and_tt_implies_tt_right, 
    rw or.comm, simp, apply hlpq, repeat {assumption}, 
    apply hlp, repeat {assumption}, 
end

lemma nec_nec_to_nec_impl {M : model} {w : wrld σ} {p q : form σ} : 
  (w ⊩⦃M⦄ ◻p) = tt → (w ⊩⦃M⦄ ◻q) = tt → (w ⊩⦃M⦄ ◻(p ⊃ q)) = tt  := 
begin
  unfold forces_form, simp at *,
  intros hp hq v wmem vmem rwv,
  rw or.comm, apply or.intro_right, apply hq, repeat {assumption}
end

lemma nec_impl_to_nec_impl_nec {M : model} {w : wrld σ} {p q : form σ} : 
  (w ⊩⦃M⦄ ◻(p ⊃ q)) = tt → (¬(w ⊩⦃M⦄ ◻p) ∨ (w ⊩⦃M⦄ ◻q) = tt) := 
begin
  intro, cases prop_decidable ((w ⊩⦃M⦄ ◻p) = tt),
  simp at h, left, simp at *, assumption,
  right, apply nec_impl_to_nec_to_nec a h
end

lemma is_true_k {M : model} {w : wrld σ} {p q : form σ} : 
  (w ⊩⦃M⦄ (◻(p ⊃ q)) ⊃ ((◻p) ⊃ ◻q)) = tt := 
impl_iff_implies.2 (λ h, impl_tt_iff_ff_or_tt.2 (nec_impl_to_nec_impl_nec h))

/- Some facts about T -/

lemma nec_to_tt {M : model} {w : wrld σ} {wm : w ∈ M.wrlds} {p : form σ} :
  (w ⊩⦃M⦄ ◻p) = tt → (w ⊩⦃M⦄ p) = tt := 
begin
  unfold forces_form, simp at *,
  intro f, apply f, repeat {assumption},
  apply M.refl, assumption
end

lemma is_true_t {M : model} {w : wrld σ} {w ∈ M.wrlds} {p : form σ} : 
  (w ⊩⦃M⦄ (◻p) ⊃ p) = tt := 
by apply impl_iff_implies.2; apply nec_to_tt; repeat {assumption}

/- Some facts about S4 -/

lemma nec_to_nec_of_nec {M : model} {w : wrld σ} {p : form σ} : 
  (w ⊩⦃M⦄ ◻p) = tt → (w ⊩⦃M⦄ ◻◻p) = tt := 
begin
  unfold forces_form, simp at *,
  intros f v wmem vmem rwv u vmem' umem rvu,
  apply f, repeat {assumption},
  refine M.trans _ _ _ _ _ _ rwv rvu,
  repeat {assumption}
end

lemma is_true_s4 {M : model} {w : wrld σ} {p : form σ} : 
  (w ⊩⦃M⦄ (◻p) ⊃ ◻◻p) = tt := 
by apply impl_iff_implies.2; apply nec_to_nec_of_nec

/- Some facts about B -/

lemma tt_to_pos_of_nec {M : model} {w : wrld σ} {p : form σ} : 
  (w ⊩⦃M⦄ p) = tt → (w ⊩⦃M⦄ ◻◇p) = tt := 
begin
  unfold forces_form, simp at *,
  intros h v vmem wmem rwv, intros f,
  apply tt_eq_ff_eq_false,
  rw (eq.symm h),
  apply f w wmem vmem,
  apply M.symm,
  exact wmem,
  exact vmem,
  exact rwv
end

lemma is_true_b {M : model} {w : wrld σ} {p : form σ} : 
  (w ⊩⦃M⦄ p ⊃ ◻◇p) = tt := 
by apply impl_iff_implies.2; apply tt_to_pos_of_nec

/- general facts about contexts -/ 

lemma ctx_tt_iff_mem_tt {Γ : ctx σ} {M : model} {w : wrld σ} :
  (w ⊩⦃M⦄ Γ) = tt ↔ (∀ p, p ∈ Γ → (w ⊩⦃M⦄ p) = tt) :=
begin
  unfold forces_ctx,
  induction (classical.prop_decidable _),
  { apply iff.intro,
    simp, intro,
    simp, assumption },
  { simp }
end

lemma mem_tt_to_ctx_tt (Γ : ctx σ) {M : model} {w : wrld σ} :
  (∀ (p : form σ) (h : p ∈ Γ), (w ⊩⦃M⦄ p) = tt) → (w ⊩⦃M⦄ Γ) = tt :=
ctx_tt_iff_mem_tt.2

lemma ctx_tt_to_mem_tt {Γ : ctx σ} {M : model} {w : wrld σ} {p : form σ} :
  (w ⊩⦃M⦄ Γ) = tt → p ∈ Γ → (w ⊩⦃M⦄ p) = tt :=
by intro; apply ctx_tt_iff_mem_tt.1; assumption

/- the empty context -/

lemma empty_ctx_tt {M : model} {w : wrld σ} : 
  (w ⊩⦃M⦄ ·) = tt :=
begin
  apply ctx_tt_iff_mem_tt.2,
  intros, exfalso, assumption
end

/- context projections -/

lemma cons_ctx_tt_iff_and {Γ : ctx σ} {M : model} {w : wrld σ} {p : form σ} : 
  (w ⊩⦃M⦄ (Γ ⸴ p)) = tt ↔ (w ⊩⦃M⦄ Γ) = tt ∧ (w ⊩⦃M⦄ p) = tt :=
begin
  unfold forces_ctx,
  induction (classical.prop_decidable (∀ p, p ∈ Γ → forces_form M p w = tt)),
  { simp, apply iff.intro,
    { intro h', exfalso, 
      apply h, intros q qmem, apply h',
      apply set.mem_insert_of_mem, assumption },
    { intros h' q qmem,
      cases h', cases qmem,
      rw qmem, assumption,
      apply h'_left, assumption } },

  { simp, apply iff.intro,
    { intro h', split,
      { assumption },
      { apply h', apply set.mem_insert } },
    { intros h' q qmem,
      cases h', cases qmem,
      rw qmem, assumption,
      apply h'_left, assumption } },
end

lemma cons_ctx_tt_to_ctx_tt {Γ : ctx σ} {M : model} {w : wrld σ} {p : form σ} : 
  (w ⊩⦃M⦄ (Γ ⸴ p)) = tt → (w ⊩⦃M⦄ Γ) = tt :=
by intro h; apply and.elim_left; apply cons_ctx_tt_iff_and.1 h

lemma ctx_tt_cons_tt_to_cons_ctx_tt {Γ : ctx σ} {M : model} {w : wrld σ} {p : form σ} : 
  (w ⊩⦃M⦄ Γ) = tt → (w ⊩⦃M⦄ p)  → (w ⊩⦃M⦄ (Γ ⸴ p)) :=
by intros hg hp; apply cons_ctx_tt_iff_and.2; split; assumption; assumption

/- sub-contexts -/

lemma ctx_tt_to_subctx_tt {Γ Δ : ctx σ} {M : model} {w : wrld σ} : 
  (w ⊩⦃M⦄ Γ) → Δ ⊆ Γ → (w ⊩⦃M⦄ Δ) :=
begin
  intros h s, 
  apply ctx_tt_iff_mem_tt.2, 
  intros p pmem,
  apply ctx_tt_iff_mem_tt.1 h,
  apply s, exact pmem
end

/- the deduction metatheorem -/

lemma sem_deduction {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⊨ₛ₅ q) → (Γ ⊨ₛ₅ p ⊃ q) :=
begin
  intro h, cases h,
  apply sem_csq.is_true,
  intros M w wmem ant,
  apply impl_iff_implies.2,
  { intro hp, apply h, assumption,
    apply ctx_tt_cons_tt_to_cons_ctx_tt, 
    repeat {assumption} }
end