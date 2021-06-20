/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic

open prf

variable {σ : nat}

namespace prf

/- identity implication -/

lemma id {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₛ₅ p ⊃ p :=
mp (mp (@pl2 σ Γ p (p ⊃ p) p) pl1) pl1

/- deduction metatheorem -/

theorem deduction {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⊢ₛ₅ q) → (Γ ⊢ₛ₅ p ⊃ q) :=
begin
  generalize eq : (Γ ⸴ p) = Γ',
  intro h,
  induction h; subst eq,
  { repeat {cases h_h},
    exact id,
    { exact mp pl1 (ax h_h) } },
  { exact mp pl1 pl1 },
  { exact mp pl1 pl2 },
  { exact mp pl1 pl3 },
  { apply mp,
    { exact (mp pl2 (h_ih_hpq rfl)) },
    { exact h_ih_hp rfl } },
  { exact mp pl1 k },
  { exact mp pl1 t },
  { exact mp pl1 s4 },
  { exact mp pl1 b },
  { exact mp pl1 (nec h_h) }
end

/- structural rules -/

lemma sub_weak {Γ Δ : ctx σ} {p : form σ} :
  (Δ ⊢ₛ₅ p) → (Δ ⊆ Γ) → (Γ ⊢ₛ₅ p) :=
begin
  intros h s,
  induction h,
  { apply ax, exact s h_h },
  { exact pl1 },
  { exact pl2 },
  { exact pl3 },
  { apply mp,
    { exact h_ih_hpq s },
    {exact h_ih_hp s} },
  { exact k },
  { exact t },
  { exact s4 },
  { exact b },
  { exact nec h_h }
end

lemma weak {Γ : ctx σ} {p q : form σ} :
  (Γ ⊢ₛ₅ p) → (Γ ⸴ q ⊢ₛ₅ p) :=
begin
  intro h,
  induction h,
  { apply ax,
    exact (set.mem_insert_of_mem _ h_h) },
  { exact pl1 },
  { exact pl2 },
  { exact pl3 },
  { apply mp,
    { exact h_ih_hpq },
    { exact h_ih_hp } },
  { exact k },
  { exact t },
  { exact s4 },
  { exact b },
  { exact nec h_h }
end

lemma contr {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⸴ p ⊢ₛ₅ q) → (Γ ⸴ p ⊢ₛ₅ q) :=
begin
  generalize eq : (Γ ⸴ p ⸴ p) = Γ',
  intro h,
  induction h; subst eq,
  { apply ax,
    cases set.eq_or_mem_of_mem_insert h_h,
    { rw h, apply set.mem_insert},
    { exact h } },
  { exact pl1 },
  { exact pl2 },
  { exact pl3 },
  { apply mp,
    { exact h_ih_hpq rfl },
    { exact h_ih_hp rfl } },
  { exact k },
  { exact t },
  { exact s4 },
  { exact b },
  { exact nec h_h }
end

lemma exg {p q r : form σ} {Γ : ctx σ} :
  (Γ ⸴ p ⸴ q ⊢ₛ₅ r) → (Γ ⸴ q ⸴ p ⊢ₛ₅ r) :=
begin
  generalize eq : (Γ ⸴ p ⸴ q) = Γ',
  intro h,
  induction h; subst eq,
  { apply ax,
    cases set.eq_or_mem_of_mem_insert h_h,
    { rw h, apply set.mem_insert_of_mem _ _,
      apply set.mem_insert _ _ },
      { cases set.eq_or_mem_of_mem_insert h with h' h',
        { rw h', apply set.mem_insert _ _ },
        { apply set.mem_insert_of_mem _ _,
          apply set.mem_insert_of_mem _ _,
          exact h' } } },
  { exact pl1 },
  { exact pl2 },
  { exact pl3 },
  { apply mp,
    { exact h_ih_hpq rfl },
    { exact h_ih_hp rfl } },
  { exact k },
  { exact t },
  { exact s4 },
  { exact b },
  { exact nec h_h }
end

/- subcontext operations -/

lemma subctx_ax {Γ Δ : ctx σ} {p : form σ} :
   Δ ⊆ Γ → (Δ ⊢ₛ₅ p) → (Γ ⊢ₛ₅ p) :=
begin
  intros s h,
  induction h,
  { apply ax (s h_h) },
  { exact pl1 },
  { exact pl2 },
  { exact pl3 },
  { apply mp,
    { exact h_ih_hpq s },
    { exact h_ih_hp s } },
  { exact k },
  { exact t },
  { exact s4 },
  { exact b },
  { exact nec h_h }
end

lemma subctx_contr {Γ Δ : ctx σ} {p : form σ}:
   Δ ⊆ Γ → (Γ ∪ Δ ⊢ₛ₅ p) → (Γ ⊢ₛ₅ p) :=
begin
  generalize eq : Γ ∪ Δ = Γ',
  intros s h,
  induction h; subst eq,
  { cases h_h,
    { exact ax h_h },
    { exact ax (s h_h) } },
  { exact pl1 },
  { exact pl2 },
  { exact pl3 },
  { apply mp,
    { exact h_ih_hpq rfl },
    { exact h_ih_hp rfl } },
  { exact k },
  { exact t },
  { exact s4 },
  { exact b },
  { exact nec h_h }
end

/- right-hand side basic rules of inference -/

lemma pr {Γ : ctx σ} {p : form σ} :
  Γ ⸴ p ⊢ₛ₅ p :=
by apply ax; apply or.intro_left; simp

lemma pr1 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⸴ q ⊢ₛ₅ p :=
by apply ax; apply or.intro_right; apply or.intro_left; simp

lemma pr2 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⸴ q ⊢ₛ₅ q :=
by apply ax; apply or.intro_left; simp

lemma by_mp1 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⸴ p ⊃ q ⊢ₛ₅ q :=
mp pr2 pr1

lemma by_mp2 {Γ : ctx σ} {p q : form σ} :
  Γ ⸴ p ⊃ q ⸴ p ⊢ₛ₅ q :=
mp pr1 pr2

lemma cut {Γ : ctx σ} {p q r : form σ} :
  (Γ ⊢ₛ₅ p ⊃ q) → (Γ ⊢ₛ₅ q ⊃ r) → (Γ ⊢ₛ₅ p ⊃ r) :=
λ hpq hqr, mp (mp pl2 (mp pl1 hqr)) hpq

lemma conv_deduction {Γ : ctx σ} {p q : form σ} :
  (Γ ⊢ₛ₅ p ⊃ q) → (Γ ⸴ p ⊢ₛ₅ q) :=
λ h, mp (weak h) pr 

/- left-hand side basic rules of inference -/

lemma mp_in_ctx_left {Γ : ctx σ} {p q r : form σ} :
  (Γ ⸴ p ⸴ q ⊢ₛ₅ r) → (Γ ⸴ p ⸴ p ⊃ q ⊢ₛ₅ r) :=
begin
  generalize eq : (Γ ⸴ p ⸴ q) = Γ',
  intros h,
  induction h; subst eq,
  { cases h_h,
    { rw h_h,
      exact by_mp1 },
    { cases h_h,
      { rw h_h,
        exact pr1 },
      { apply ax,
        apply set.mem_insert_of_mem _ _,
        apply set.mem_insert_of_mem _ _, exact h_h } } },
    { exact pl1 },
    { exact pl2 },
    { exact pl3 },
    { apply mp,
      { exact h_ih_hpq rfl },
      { exact h_ih_hp rfl } },
    { exact k },
    { exact t },
    { exact s4 },
    { exact b },
    { exact nec h_h }
end

lemma mp_in_ctx_right {Γ : ctx σ} {p q r : form σ} :
  (Γ ⸴ p ⸴ p ⊃ q ⊢ₛ₅ r) → (Γ ⸴ p ⸴ q ⊢ₛ₅ r) :=
begin
  generalize eq : (Γ ⸴ p ⸴ p ⊃ q) = Γ',
  intros h,
  induction h; subst eq,
  { cases h_h,
    { subst h_h,
      exact mp pl1 pr },
    { cases h_h,
      { subst h_h,
        exact pr1 },
      { exact weak (weak (ax h_h)) } } },
    { exact pl1 },
    { exact pl2 },
    { exact pl3 },
    { apply mp,
      { exact h_ih_hpq rfl },
      { exact h_ih_hp rfl } },
    { exact k },
    { exact t },
    { exact s4 },
    { exact b },
    { exact nec h_h }
end

/- basic lemmas -/

lemma contrap {Γ : ctx σ} {p q : form σ} :
  Γ ⊢ₛ₅ ((~q) ⊃ (~p)) ⊃ (p ⊃ q) :=
deduction (deduction (mp (mp pl3 pr1) (mp pl1 pr2) ))

lemma not_impl {Γ : ctx σ} {p q : form σ} : 
  Γ ⊢ₛ₅ (p ⊃ q) ⊃ ((~q) ⊃ (~p)) :=
begin
  repeat { apply deduction },
  apply mp,
  { exact pr1 },
    apply mp,
    { apply ax,
      apply set.mem_insert_of_mem,
      apply set.mem_insert_of_mem,
      apply set.mem_insert },
    { exact pr2 }
end

lemma dne {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₛ₅ (~~p) ⊃ p :=
have h : Γ ⊢ₛ₅ (~~p) ⊃ ((~p) ⊃ (~p)) := mp pl1 id,
mp (mp pl2 (cut pl1 pl3)) h

lemma dni {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₛ₅ p ⊃ (~~p) :=
mp contrap dne

lemma lem {p : form σ} {Γ : ctx σ} :
  Γ ⊢ₛ₅ p ∨ ~p :=
mp dni (mp contrap dne)

lemma not_impl_to_and {p q : form σ} {Γ : ctx σ} :
  Γ ⊢ₛ₅ (~(p ⊃ q)) ⊃ (p & (~q)) :=
begin
  repeat {apply deduction},
  apply (mp pr1),
  { apply deduction,
    apply mp,
    { apply dne },
    { exact (mp pr1 pr2) } },
end

lemma and_not_to_not_impl {p q : form σ} {Γ : ctx σ} :
  Γ ⊢ₛ₅ (p & (~q)) ⊃ ~(p ⊃ q) :=
begin
  repeat {apply deduction},
  apply mp,
  { apply pr1 },
  { apply cut,
    { apply pr2 },
    { apply dni } }
end

/- basic modal lemmas (K and B) -/

lemma box_contrap {p q : form σ} :
 · ⊢ₛ₅ (◻(p ⊃ q)) ⊃ (◻((~q) ⊃ ~p)) :=
prf.mp (prf.k) (prf.nec prf.not_impl)

lemma diamond_k {p q : form σ} :
 · ⊢ₛ₅ (◻(p ⊃ q)) ⊃ ((◇p) ⊃ (◇q)) :=
prf.deduction $ prf.mp prf.not_impl
(prf.mp prf.k (prf.mp (prf.weak box_contrap) prf.pr ))

lemma box_dne {p : form σ} :
 · ⊢ₛ₅ (◻~~p) ⊃ (◻p) :=
prf.mp (prf.k) (prf.nec (prf.dne))

lemma box_dni {p : form σ} :
 · ⊢ₛ₅ (◻p) ⊃ (◻~~p) :=
prf.mp (prf.k) (prf.nec (prf.dni))

lemma not_box_dni {p : form σ} :
 · ⊢ₛ₅ (~◻p) ⊃ (~◻~~p) :=
prf.mp prf.not_impl box_dne

lemma not_box_dne {p : form σ} :
 · ⊢ₛ₅ (~◻~~p) ⊃ (~◻p) :=
prf.mp prf.not_impl box_dni

lemma diamond_dne {p : form σ} :
 · ⊢ₛ₅ (◇~~p) ⊃ (◇p) :=
not_box_dne

lemma diamond_dni {p : form σ} :
 · ⊢ₛ₅ (◇p) ⊃ (◇~~p) :=
not_box_dni

lemma contrap_b {p : form σ} :
 · ⊢ₛ₅ (◇◻p) ⊃ p :=
begin
  apply prf.cut,
  show (· ⊢ₛ₅ (◇◻p) ⊃ (~◻~◻~~p)),
    from @prf.mp _ _ (◻(◻p ⊃ ◻(~~p))) _ diamond_k (prf.nec box_dni),
  apply prf.cut,
  show (· ⊢ₛ₅ (~◻~◻~~p) ⊃ ~~p),
    from prf.mp prf.not_impl prf.b,
  apply prf.dne
end

/- notable introduction rules -/

lemma negintro {p q : form σ} {Γ : ctx σ} :
  (Γ ⊢ₛ₅ p ⊃ q) → (Γ ⊢ₛ₅ p ⊃ ~q) → (Γ ⊢ₛ₅ ~p) :=
have h : ∀ q, (Γ ⊢ₛ₅ p ⊃ q) → (Γ ⊢ₛ₅ (~~p) ⊃ q) := λ q h, cut dne h,
  λ hp hnp, mp (mp pl3 (h (~q) hnp)) (h q hp)

lemma ex_falso {Γ : ctx σ} {p : form σ} :
  (Γ ⊢ₛ₅ ⊥) → (Γ ⊢ₛ₅ p) :=
begin
  intro h,
  apply mp,
  { exact dne },
  { apply mp,
    { exact pl1 },
    { exact h } }
end

lemma ex_falso_and {Γ : ctx σ} {p q : form σ} :
  Γ ⊢ₛ₅ (~p) ⊃ (p ⊃ q) :=
begin
  repeat {apply deduction},
  apply ex_falso,
  exact (mp pr1 pr2)
end

lemma ex_falso_pos {Γ : ctx σ} {p q : form σ} :
  Γ ⊢ₛ₅ p ⊃ ((~p) ⊃ q) :=
begin
  repeat {apply deduction},
  apply mp,
  { apply mp,
    { apply ex_falso_and },
    { exact pr2 } },
  { exact pr1 },
end

lemma contr_conseq {Γ : ctx σ} {p r : form σ} :
  Γ ⊢ₛ₅ (p ⊃ r) ⊃ (((~p) ⊃ r) ⊃ r) :=
begin
  repeat {apply deduction},
  apply mp,
  { apply mp,
    { apply pl3, exact p },
    { apply mp,
      { apply not_impl },
      { exact pr1 } } },
  { apply cut,
    { apply mp,
      { apply not_impl,
        exact (~p) },
      { apply pr2 } },
        apply dne }
end

lemma impl_weak {p q r : form σ} {Γ : ctx σ} (h : (Γ ⸴ r ⊢ₛ₅ p) → (Γ ⊢ₛ₅ p)) :
  ((Γ ⊢ₛ₅ p) → (Γ ⊢ₛ₅ q)) → ((Γ ⸴ r ⊢ₛ₅ p) → (Γ ⸴ r ⊢ₛ₅ q)) :=
λ hpq hp, weak (hpq (h hp))

lemma and_intro {Γ : ctx σ} {p q : form σ} :
  (Γ ⊢ₛ₅ p) → (Γ ⊢ₛ₅ q) → (Γ ⊢ₛ₅ (p & q)) :=
begin
  intros hp hq,
  apply deduction,
  apply mp,
    apply mp,
    { apply pr },
    repeat { apply weak, assumption }
end


lemma and_elim_left {p q : form σ} {Γ : ctx σ} :
  (Γ ⸴ (p & q) ⊢ₛ₅ p) :=
begin
  apply mp,
  { apply dne },
  { apply mp,
    { apply mp,
      { apply pl2, exact (p ⊃ (q ⊃ ⊥)) },
      { apply mp,
        { apply pl1 },
        { exact pr } } },
    { exact ex_falso_and } }
end

lemma and_elim_right {p q : form σ} {Γ : ctx σ} :
  (Γ ⸴ (p & q) ⊢ₛ₅ q) :=
begin
  apply mp,
  { apply dne },
  { apply mp,
    { apply mp,
      { apply pl2, exact (p ⊃ (q ⊃ ⊥)) },
      { apply mp,
        { apply pl1 },
        { exact pr } } },
    repeat {apply deduction},
    apply mp,
    { apply ax,
      apply set.mem_insert_of_mem,
      apply set.mem_insert_of_mem,
      apply set.mem_insert },
    { exact pr2 } }
end

lemma or_intro_left {Γ : ctx σ} {p q r : form σ} :
  (Γ ⊢ₛ₅ p) → (Γ ⊢ₛ₅ (p ∨ q)) :=
begin
  intros hp, simp,
  apply mp,
  { apply dni },
  { apply deduction,
    { apply mp,
      { apply mp,
        { apply ex_falso_and },
        { exact pr } },
      { apply weak, assumption } } }
end

lemma or_intro_right {Γ : ctx σ} {p q r : form σ} :
  (Γ ⊢ₛ₅ q) → (Γ ⊢ₛ₅ (p ∨ q)) :=
begin
  intros hp, simp,
  apply mp,
  { apply dni },
  { apply deduction,
    { apply mp,
      { apply dni },
      {apply weak, assumption } } }
end

lemma or_elim {Γ : ctx σ} {p q r : form σ} :
  (Γ ⊢ₛ₅ (p ∨ q)) → (Γ ⊢ₛ₅ p ⊃ r) → (Γ ⊢ₛ₅ q ⊃ r) → (Γ ⊢ₛ₅ r) :=
begin
  intros hpq hpr hqr,
  apply mp,
    { apply mp,
      { apply contr_conseq, exact p },
      { assumption } },
    { apply cut,
      { apply mp,
        { apply dne },
        { assumption } },
      { apply cut,
        exact dne,
        assumption } }
end

lemma detach_pos {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ p ⊢ₛ₅ q) → (Γ ⸴ ~p ⊢ₛ₅ q) → (Γ ⊢ₛ₅ q) :=
begin
  intros hpq hnpq,
  apply or_elim,
  { apply lem },
  repeat {apply deduction, assumption}
end

lemma detach_neg {Γ : ctx σ} {p q : form σ} :
  (Γ ⸴ ~p ⊢ₛ₅ q) → (Γ ⸴ p ⊢ₛ₅ q) → (Γ ⊢ₛ₅ q) :=
begin
  intros hpq hnpq,
  apply or_elim,
  { apply lem },
  { apply deduction, exact hnpq },
  { apply deduction, assumption }
end

end prf