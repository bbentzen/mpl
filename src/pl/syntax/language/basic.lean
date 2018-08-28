/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

definition var : ℕ → Type := fin

/- language definition -/

variable σ : nat

inductive form : Type
| atom : var σ → form
| bot : form
| impl : form → form → form 

notation `#` := form.atom
notation `⊥` := form.bot _
notation `~` p := (form.impl p (form.bot _))
notation p `⊃` q := (form.impl p q)
notation p `&` q := (~ (p ⊃ ~q))
notation p `∨` q := ~ (~p & ~q)