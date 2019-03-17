/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

variable σ : nat

/- language definition -/

inductive form : Type
| atom : fin σ → form
| bot : form
| impl : form → form → form 
| box : form → form

prefix `#` := form.atom
notation `⊥` := form.bot _
infix `⊃` := form.impl
notation `~`:40 p := form.impl p (form.bot _)
notation p `&` q := ~(p ⊃ ~q)
notation p `∨` q := ~(~p & ~q)
prefix `◻`:80 := form.box
prefix `◇`:80 := λ p, ~(◻ (~ p))