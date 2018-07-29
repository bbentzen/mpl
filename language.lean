/-
Copyright (c) 2015 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

namespace mpl
open list nat

/- language -/

inductive form : Type
| var : nat → form
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

notation Γ `∪` p := cons p Γ

inductive k.prf : ctx → form → Type 
| ax {Γ : ctx} {p : form} : k.prf (Γ ∪ p) p
| exg {Γ : ctx} {p q r: form} (d : k.prf (Γ ∪ p ∪ q) r) : k.prf (Γ ∪ q ∪ p) r
| ni {Γ : ctx} {p : form} (d₁ : k.prf Γ p) (d₁ : k.prf Γ (p & ~p)):  k.prf Γ ~p
| raa {Γ : ctx} {p : form} (d₁ : k.prf Γ ~p) (d₂ : k.prf Γ (p & ~p)) : k.prf Γ p
| dt {Γ : ctx} {p q : form} (d : k.prf (Γ ∪ p) q) : k.prf Γ (p ⊃ q)
| mp {Γ : ctx}  {p q : form} (d₁ : k.prf Γ p) (d₂: k.prf Γ (p ⊃ q)) : k.prf Γ q
| k {Γ : ctx}  {p q : form} (d : k.prf Γ ◻(p ⊃ q)) : k.prf Γ (◻p ⊃ ◻q)
| nec {p : form} (d : k.prf nil p) : k.prf nil (◻p)

notation . := nil
notation Γ `⊢ₖ` p := k.prf Γ p
notation α `⇒` β := α → β

example (p q : form) :
  . ⊢ₖ p ⊃ (q ⊃ p) := 
k.prf.dt (k.prf.dt (k.prf.exg k.prf.ax))

example (p q : form) :
 . ⊢ₖ ◻ p ⊃ ◻ (q ⊃ p) := 
k.prf.k (k.prf.nec (k.prf.dt (k.prf.dt (k.prf.exg k.prf.ax))))

end mpl
