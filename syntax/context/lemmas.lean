/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .basic ..language.basic ..language.lemmas

definition exg : ctx → ctx :=
begin
  intro Γ,
    induction Γ with p Γ IH,
      exact ·,
      induction Γ with q Γ IH,
        exact (· ⸴ p),
        exact (Γ ⸴ p ⸴ q)
end
