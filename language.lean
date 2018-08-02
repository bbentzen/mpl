/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

namespace mpl
open list nat bool

/- language -/

definition var : Type := nat

inductive form : Type
| atom : var → form
| neg : form → form
| impl : form → form → form 
| box : form → form

notation `~` p := form.neg p
notation p `⊃` q := form.impl p q
notation `◻` p := form.box p
notation `◇` p := ~ ◻ ~ p
notation p `&` q := ~ (p ⊃ ~q)
notation p `∨` q := ~ (~p & ~q)

/- the K system -/

def ctx : Type := list form

notation Γ `⸴` p := cons p Γ
notation Γ `∪` Ψ := append Γ Ψ
notation `{` p `}` := [p]  

inductive prf : ctx → form → Type 
| pl1 {Γ : ctx} {p q : form} : prf Γ (p ⊃ (q ⊃ p))
| pl2 {Γ : ctx} {p q r : form} : prf Γ ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))
| pl3 {Γ : ctx} {p q : form} :  prf Γ (((~p) ⊃ ~q) ⊃ ((~p ⊃ q) ⊃ p))
| mp {Γ : ctx}  {p q : form} (d₁: prf Γ (p ⊃ q)) (d₂ : prf Γ p) : prf Γ q
| k {Γ : ctx}  {p q : form} : prf Γ ((◻(p ⊃ q)) ⊃ (◻p ⊃ ◻q))
| nec {Γ : ctx} {p : form} (d : prf nil p) : prf Γ (◻p)

axiom ax {Γ : ctx} {p : form} : prf (Γ ⸴ p) p

notation `·` := nil
notation Γ `⊢ₖ` p := prf Γ p
notation α `⇒` β := α → β 

def deduction {Γ : ctx} (p q : form) :
  (Γ ⸴ p ⊢ₖ q) ⇒ (Γ ⊢ₖ p ⊃ q) :=
begin
 intro H,
 induction H,
   exact prf.mp prf.pl1 prf.pl1,
   exact prf.mp prf.pl1 (prf.pl2),
   exact prf.mp prf.pl1 (prf.pl3),
   exact prf.mp (prf.mp prf.pl2 H_ih_d₁) H_ih_d₂,
   exact prf.mp prf.pl1 prf.k,
   exact prf.mp prf.pl1 (prf.nec H_d)
end

-- Maybe I can group up the following 'begin ... end' block and encapsulate it in a new tactic?

def weak (p q : form) (Γ : ctx):
  (Γ ⊢ₖ p) ⇒ (Γ ⸴ q ⊢ₖ p) :=
begin
  intro H,
  induction H,
    exact prf.pl1,
    exact prf.pl2,
    exact prf.pl3,
    exact prf.mp H_ih_d₁ H_ih_d₂,
    exact prf.k,
    exact prf.nec H_d
end

def contr (p q : form) (Γ : ctx):
  (Γ ⸴ p ⸴ p ⊢ₖ q) ⇒ (Γ ⸴ p ⊢ₖ q) :=
begin
  intro H,
  induction H,
    exact prf.pl1,
    exact prf.pl2,
    exact prf.pl3,
    exact prf.mp H_ih_d₁ H_ih_d₂,
    exact prf.k,
    exact prf.nec H_d
end

def exg (p q r : form) (Γ : ctx):
  (Γ ⸴ p ⸴ q ⊢ₖ r) ⇒ (Γ ⸴ q ⸴ p ⊢ₖ r) :=
begin
  intro H,
  induction H,
    exact prf.pl1,
    exact prf.pl2,
    exact prf.pl3,
    exact prf.mp H_ih_d₁ H_ih_d₂,
    exact prf.k,
    exact prf.nec H_d
end

/- Kripke models -/

definition frame : Type := ((list nat) × (nat → nat → bool))

definition k_model : Type := frame × (nat → var → bool)

notation `𝓦` `⸴` `𝓡` `⸴` `𝓿` := k_model

def true_in_wrld (M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)) : form → nat → bool
| # p     := λ w, M.snd w p --nat.rec_on (M.fst.fst) tt (λ _ _, M.snd w p)
| ~ p     := λ w, bnot (true_in_wrld p w)
| (p ⊃ q) := λ w, (bnot (true_in_wrld p w)) || (true_in_wrld q w) 
| ◻ p    := λ w, 
    nat.rec_on M.fst.fst tt 
    (λ v IH, IH && ((bnot (M.fst.snd w v)) || (true_in_wrld p v)))

notation M `⦃`p`⦄` w := true_in_wrld M p w

inductive stsf (M : (𝓦 ⸴ 𝓡 ⸴ 𝓿) ) (p : form) : Type 
| is_true (m : Π (w : nat),  (M ⦃p⦄ w) = tt ) : stsf

notation M `⊨ₖ` p := stsf M p

definition sndnss (p : form) (M : (𝓦 ⸴ 𝓡 ⸴ 𝓿) ) :
( · ⊢ₖ p) ⇒ (M ⊨ₖ p) :=
begin
  intro H,
  induction H,
    repeat {
      apply stsf.is_true,
        intros w,
        unfold true_in_wrld,
        induction (true_in_wrld M H_p w), 
          induction (true_in_wrld M H_q w),
            simp, simp,
          induction (true_in_wrld M H_q w),
            simp, simp
    },
          induction (true_in_wrld M H_r w),
            simp, simp,
    
    apply stsf.is_true,
      induction H_ih_d₁, 
        induction H_ih_d₂,
          intros w,
          apply eq.symm,
            exact (
              calc 
                tt  = M⦃H_p ⊃ H_q⦄w  : eq.symm (H_ih_d₁ w)
                ... = bnot (M⦃H_p⦄w)  || M⦃H_q⦄w  : rfl
                ... = ff  || M⦃H_q⦄w  : eq.substr (H_ih_d₂ w) rfl
                ... = M⦃H_q⦄w  : ff_bor _
            ),
    apply stsf.is_true,
      unfold true_in_wrld,      
      intro w,
          induction M.fst.fst with k IH,
            simp, simp at *,
            cases IH,
              apply or.intro_left,
                  apply or.intro_left,
                    assumption,                    
                  apply or.intro_right,
                  sorry, -- proof of K goes here

    apply stsf.is_true,
      intro w, 
      unfold true_in_wrld,
      induction H_ih,
        induction M.fst.fst with k IH,
          simp, simp,
          apply and.intro,
            exact IH,
            induction ((M.fst).snd w k), 
              simp, simp,
              exact (H_ih k)
end

def nec_false_exist_wrld_false (M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)) (w : nat) (p : form) : 
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

def all_wrlds_true_nec_true (M : (𝓦 ⸴ 𝓡 ⸴ 𝓿)) (w : nat) (p : form) : 
(∀ v, ((M.fst.snd w v = tt) → (M⦃p⦄v) = tt)) ⇒ ((M⦃◻p⦄w) = tt)  := 
begin
  intro f,
  apply eq_tt_of_not_eq_ff,
  apply 
    (show ¬ (∃ v, (_ = tt) ∧ (_ = ff)) ⇒ ¬ (_ = ff) , 
      from λ f a, f ((nec_false M w p) a) ),
    intro g, 
    cases g with v h,
      cases h with h1 h2,
        exact (bool.no_confusion (eq.trans (eq.symm (f v h1)) h2))
end

end mpl
