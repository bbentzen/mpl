/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic

/- lemmas -/

definition atom.code (α : nat) : form → Prop
 | (#v) := (α = v)
 | (~p) := false
 | (p ⊃ q) := false
 | (◻p) := false

definition atom.encode (α : nat) (x : form) : (#α) = x → atom.code α x :=
by intro h; induction h; unfold atom.code

definition neg.code (α : form) : form → Prop
 | (#v) := false
 | (~p) := (α = p)
 | (p ⊃ q) := false
 | (◻p) := false

definition neg.encode (α x : form) : (~α) = x → neg.code α x :=
by intro h; induction h; unfold neg.code

definition impl.code (α β : form) : form → Prop
 | (#v) := false
 | (~p) := false
 | (p ⊃ q) := (α = p) ∧ (β = q)
 | (◻p) := false

definition impl.encode (α β x : form) : (α ⊃ β) = x → impl.code α β x :=
by intro h; induction h; unfold impl.code;  apply and.intro; simp

definition box.code (α : form) : form → Prop
 | (#v) := false
 | (~p) := false
 | (p ⊃ q) := false
 | (◻p) := (α = p)

definition box.encode (α x : form) : (◻α) = x → box.code α x :=
by intro h; induction h; unfold box.code

/- injectivity -/

definition atom.eq (v w : nat) :
  (#v) = (#w) → v = w :=
by apply atom.encode

definition neg.eq (p q : form) :
   (~p) = (~q) → p = q :=
by apply neg.encode

definition impl.eq (p₁ p₂ q₁ q₂ : form) :
  (p₁ ⊃ p₂) = (q₁ ⊃ q₂) → (p₁ = q₁) ∧ (p₂ = q₂) :=
by apply impl.encode

definition box.eq (p q : form) :
   (◻p) = (◻q) → p = q :=
by apply box.encode

/- decidability of equality -/

open tactic

def dec_eq_nat : decidable_eq nat :=
by mk_dec_eq_instance

def dec_eq_form :
  Π (p q : form), (p = q) ∨ (p ≠ q) :=
begin
  intros p,
  induction p,
    intro q,
    induction q,
      cases (dec_eq_nat p q),
        apply or.intro_right,
          intro ne,
          apply h,
            apply (atom.encode p (#q)),
            assumption,
        apply or.intro_left,
          induction h,
          exact rfl, 
      
      repeat{
        apply or.intro_right,
          exact (λ H, form.no_confusion H)
      },

    intro q,
    induction q,
      apply or.intro_right,
        exact (λ H, form.no_confusion H),

      cases (p_ih q_a),
        apply or.intro_left,
          induction h,
            exact rfl, 
        apply or.intro_right,
          intro ne,
          apply h,
            apply (neg.encode p_a (~q_a)),
            assumption,

      repeat{
        apply or.intro_right,
          exact (λ H, form.no_confusion H)
      },

    intro q,
    induction q,

      repeat {
        apply or.intro_right,
          exact (λ H, form.no_confusion H)
      },

      cases (p_ih_a q_a),
        cases (p_ih_a_1 q_a_1),
          apply or.intro_left,
            induction h,
              induction h_1,
                exact rfl, 
              apply or.intro_right,
                intro ne,
                cases (impl.encode p_a p_a_1 (q_a ⊃ q_a_1) ne),
                  contradiction,
        cases (p_ih_a_1 q_a_1),
          repeat {
            apply or.intro_right,
              intro ne,
              cases (impl.encode p_a p_a_1 (q_a ⊃ q_a_1) ne),
                contradiction
          },

    intro q,
    induction q,

      repeat {
        apply or.intro_right,
          exact (λ H, form.no_confusion H)
      },

      cases (p_ih q_a),
        apply or.intro_left,
          induction h,
            exact rfl, 
        apply or.intro_right,
          intro ne,
          apply h,
            apply (box.encode p_a (◻q_a)),
            assumption,

end

-- example (p q : nat) : (p ≠ q) → (#p) ≠ (#q) :=
-- begin
--  intros ne h,
--  apply ne, apply (atom.encode p (#q)), assumption
--end
