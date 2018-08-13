/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

/- language definition -/

inductive form : Type
| atom : nat → form
| neg : form → form
| impl : form → form → form 
| box : form → form

notation `#` v := form.atom v
notation `~` p := form.neg p
notation p `⊃` q := form.impl p q
notation `◻` p := form.box p
notation `◇` p := (~ (◻ (~ p)))
notation p `&` q := (~ (p ⊃ ~q))
notation p `∨` q := ~ (~p & ~q)
