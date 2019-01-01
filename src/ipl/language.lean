/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

--import .basic

definition var : ℕ → Type := fin

variable σ : nat

/- language definition -/

inductive form : Type
| atom : var σ → form
| bot : form
| and : form → form → form 
| or : form → form → form
| impl : form → form → form

notation `#` := form.atom
notation `⊥` := form.bot _
notation p `&` q := form.and p q
notation p `∨` q := form.or p q
notation p `⊃` q := form.impl p q
notation `~` p := (form.impl p (form.bot _))

