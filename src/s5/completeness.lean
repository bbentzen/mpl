/-
Copyright (c) 2018 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");
Author: Bruno Bentzen
-/

import .consistency ..encode

open nat set classical

local attribute [instance, priority 0] prop_decidable

variables {σ : nat}

/- maximal set of a context -/

namespace ctx
def is_max (Γ : ctx σ) := is_consist Γ ∧ ∀ p, p ∈ Γ ∨ (~p) ∈ Γ

def insert_form (Γ : ctx σ) (p : form σ) : ctx σ :=
if is_consist (Γ ⸴ p) then Γ ⸴ p else Γ ⸴ ~p

def insert_code (Γ : ctx σ) (n : nat) : ctx σ :=
match encodable.decode (form σ) n with
| none := Γ
| some p := insert_form Γ p
end

@[simp]
def maxn (Γ : ctx σ) : nat → ctx σ
| 0     := Γ
| (n+1) := insert_code (maxn n) n

@[simp]
def max (Γ : ctx σ) : ctx σ := 
⋃ n, maxn Γ n

/- maximal extensions are extensions -/

lemma subset_insert_code {Γ : ctx σ} (n) : 
  Γ ⊆ insert_code Γ n :=
begin
  intros v hv,
  unfold insert_code,
  cases (encodable.decode (form σ) _); unfold insert_code insert_form,
  { assumption },
  { split_ifs; exact set.mem_insert_of_mem _ hv },
end

lemma subset_maxn {Γ : ctx σ} : 
  ∀ n, Γ ⊆ maxn Γ n
| 0        := by refl
| (succ n) := subset.trans (subset_maxn n) (subset_insert_code _)

lemma maxn_subset_max {Γ : ctx σ} (n) : 
  maxn Γ n ⊆ max Γ :=
subset_Union _ _

lemma subset_max_self {Γ : ctx σ} :
  Γ ⊆ max Γ :=
maxn_subset_max 0

lemma maxn_subset_succ {Γ : ctx σ} {n : nat} :
  maxn Γ n ⊆ maxn Γ (n+1) :=
subset_insert_code _

lemma maxn_mono {Γ : ctx σ} {m n : nat} (h : n ≤ m) :
  maxn Γ n ⊆ maxn Γ m :=
by induction h; [refl, exact subset.trans h_ih (subset_insert_code _)]

/- maximal extensions are maximal -/

lemma insert_form_self {Γ : ctx σ} {p : form σ} : 
  p ∈ insert_form Γ p ∨ (~p) ∈ insert_form Γ p :=
begin
  unfold insert_form, split_ifs,
  { exact or.inl (mem_insert _ _) },
  { exact or.inr (mem_insert _ _) },
end

lemma insert_code_self {Γ : ctx σ} (p : form σ) : 
  p ∈ insert_code Γ (encodable.encode p) ∨ (~p) ∈ insert_code Γ (encodable.encode p) :=
begin
  unfold insert_code,
  rw (encodable.encodek p),
  apply insert_form_self,
end

lemma mem_or_mem_max {Γ : ctx σ} (p : form σ) : 
  p ∈ max Γ ∨ (~p) ∈ max Γ :=
begin
  have := maxn_subset_max (encodable.encode p + 1),
  exact (insert_code_self p).imp (@this _) (@this _),
end

/- maximal extensions preserves consistency -/

lemma is_consist_insert_form {Γ : ctx σ} {p : form σ} 
  (H : is_consist Γ) : is_consist (insert_form Γ p) :=
begin
  rw insert_form, split_ifs,
  { exact h },
  { exact inconsist_to_neg_consist H h },
end

lemma is_consist_insert_code {Γ : ctx σ} (n)
  (H : is_consist Γ) : is_consist (insert_code Γ n) :=
begin
  rw insert_code, cases encodable.decode _ _,
  { exact H },
  { exact is_consist_insert_form H }
end

lemma is_consist_maxn {Γ : ctx σ} : 
  ∀ n, is_consist Γ → is_consist (maxn Γ n)
| 0 H := H
| (n+1) H := is_consist_insert_code _ (is_consist_maxn _ H)

lemma in_ext_ctx_max_set_is_in_ext_ctx_at {Γ : ctx σ} {p : form σ} :
  (p ∈ max Γ) → ∃ n, p ∈ maxn Γ n :=
mem_Union.1

lemma ext_ctx_lvl {Γ : ctx σ} {p : form σ} :
  (max Γ ⊢ₛ₅ p) → ∃ n, maxn Γ n ⊢ₛ₅ p :=
begin
  generalize eq : max Γ = Γ',
  intro h, induction h; subst eq,
    { cases in_ext_ctx_max_set_is_in_ext_ctx_at h_h,
      constructor, 
      apply prf.ax, 
      assumption },

    repeat {
      constructor,
      apply prf.pl1 <|> apply prf.pl2 <|> apply prf.pl3,
      exact 0
    },
    
    { cases h_ih_hpq rfl with n0 h_ext_pq, 
      cases h_ih_hp rfl with n1 h_ext_p,
        cases (prop_decidable (n0 ≤ n1)),
            have hh: n1 ≤ n0 :=
              begin
                cases nat.le_total, 
                assumption, 
                contradiction 
            end,
          constructor,
            apply prf.mp,
            assumption,
              apply prf.sub_weak,
                exact h_ext_p,
                apply maxn_mono,
                assumption,
          constructor,
            apply prf.mp,
              apply prf.sub_weak,
                exact h_ext_pq,
                apply maxn_mono,
                assumption,
              assumption },

    { constructor,
      apply prf.k,
      exact 0 },

    { constructor,
      apply prf.t,
      exact 0 },
    
    { constructor,
      apply prf.s4,
      exact 0 },
    
    { constructor,
      apply prf.b,
      exact 0 },
    
    { constructor,
      apply prf.nec h_h,
      exact 0 }
end

lemma is_consist_max {Γ : ctx σ} :
  is_consist Γ → is_consist (max Γ) :=
λ hc nc, let ⟨n, ht⟩ := ext_ctx_lvl nc in is_consist_maxn _ hc ht

/- maximal consistent sets are closed under derivability -/

lemma max_of_max {Γ : ctx σ} {p : form σ} (h : is_consist Γ) : is_max (max Γ) :=
⟨ is_consist_max h , mem_or_mem_max⟩ 

lemma mem_max_of_prf {Γ : ctx σ} {p : form σ} (h₁ : is_max Γ)
  (h₂ : Γ ⊢ₛ₅ p) : p ∈ Γ :=
(h₁.2 p).resolve_right $ λ hn,
h₁.1 (prf.mp (prf.ax hn) h₂)

end ctx

/- the canonical model construction -/

-- domain

namespace canonical
def domain (σ : nat) : set (wrld σ) := {w | ctx.is_max w}

lemma mem_domain_max {w : wrld σ} :
  w ∈ domain σ → ∀ p, (p ∈ w) ∨ ((~p) ∈ w) :=
and.right

lemma mem_domain_consist {w : wrld σ} :
  w ∈ domain σ → is_consist w :=
and.left

lemma mem_domain {w : wrld σ}
  (h : is_consist w) : ctx.max w ∈ domain σ :=
⟨ctx.is_consist_max h, ctx.mem_or_mem_max⟩

lemma mem_domain_of_prf {p : form σ} (w ∈ domain σ)
  (h : w ⊢ₛ₅ p) : p ∈ w :=
(mem_domain_max H p).resolve_right $
λ hn, (mem_domain_consist H) (prf.mp (prf.ax hn) h)

-- accessibility

def unbox (w : wrld σ) : wrld σ := {p | (◻p) ∈ w}

noncomputable def access : wrld σ → wrld σ → bool :=
assume w v, if (unbox w ⊆ v) then tt else ff

lemma subset_unbox_iff_access {w v : wrld σ} : access w v = tt ↔ unbox w ⊆ v :=
by unfold access; simp 

lemma mem_unbox_iff_mem_box {p : form σ} {w : wrld σ} :
  p ∈ unbox w ↔ (◻p) ∈ w :=
⟨ id, id ⟩ 

lemma not_mem_unbox_of_mem_not_box {p : form σ} {w : wrld σ} (hc : w ∈ domain σ) :
  (~◻p) ∈ w → p ∉ unbox w :=
λ h np, (mem_domain_consist hc) (prf.mp (prf.ax h) (prf.ax (mem_unbox_iff_mem_box.1 np)))

lemma mem_box_of_unbox_prf {p : form σ} {w : wrld σ} (H : w ∈ domain σ) :
  (unbox w ⊢ₛ₅ p) → (◻p) ∈ w :=
begin
  generalize eq : unbox w = Γ',
  intro h, induction h; subst eq,
    { assumption },
    repeat { apply ctx.mem_max_of_prf H,
      apply prf.nec,
      apply prf.pl1 <|> apply prf.pl2 <|> apply prf.pl3 },
    { apply ctx.mem_max_of_prf H,
      refine prf.mp (prf.ax _) (prf.ax (h_ih_hp rfl)),
      exact (ctx.mem_max_of_prf H) (prf.mp prf.k (prf.ax (h_ih_hpq rfl))) },
    { apply ctx.mem_max_of_prf H,
      exact prf.nec prf.k },
    { apply ctx.mem_max_of_prf H,
      exact prf.nec prf.t },
    { apply ctx.mem_max_of_prf H,
      exact prf.nec prf.s4 },
    { apply ctx.mem_max_of_prf H,
      exact prf.nec prf.b },
    { apply ctx.mem_max_of_prf H,
      apply prf.nec (prf.nec h_h) }
end

lemma not_unbox_prf_of_not_box_mem {p : form σ} {w : wrld σ} (hw : w ∈ domain σ) :
  (~◻p) ∈ w → (unbox w ⊬ₛ₅ p) :=
by { intros h nhp, apply mem_domain_consist hw, apply prf.mp (prf.ax h) (prf.ax (mem_box_of_unbox_prf hw nhp)) }

lemma consist_unbox_of_not_box_mem {p : form σ} {w : wrld σ} (hw : w ∈ domain σ) :
  (~◻p) ∈ w → is_consist (unbox w ⸴ (~p)) :=
λ hn, consist_not_of_not_prf (not_unbox_prf_of_not_box_mem hw hn)

-- valuation

noncomputable def val : fin σ → wrld σ → bool :=
assume p w, if w ∈ domain σ ∧ (#p) ∈ w then tt else ff

-- reflexivity

lemma access.refl :
  ∀ w ∈ domain σ, access w w = tt :=
begin
  intros w h, unfold access,
  simp, intros p hp, cases mem_domain_max h p,
  { assumption },
  { exfalso, apply mem_domain_consist h,
    apply prf.mp,
    { apply prf.ax h_1 }, 
    { apply prf.mp,
      { apply prf.t },
      { apply prf.ax,
        apply mem_unbox_iff_mem_box.1,
        assumption } } }
end

-- symmetry

lemma access.symm : ∀ w ∈ domain σ, ∀ v ∈ domain σ, access w v = tt → access v w = tt :=
begin
  intros w hw v hv, unfold access,
  simp, intros sw p hp,
  apply mem_domain_of_prf _ hw,
  apply prf.mp,
    { apply prf.sub_weak, apply prf.contrap_b, simp },
    { have h₁ : ∀ p, p ∉ v → p ∉ unbox w, from 
      (λ p, (@not_imp_not _ _ (prop_decidable _)).2 (@sw _ ) ),
      have h₂ : (◻~◻p) ∉ w, from 
      begin
        apply h₁,
        intro h, apply mem_domain_consist hv,
        apply prf.mp,
        { apply prf.ax h }, 
        { apply prf.ax, assumption }
      end,
      cases mem_domain_max hw (◻~◻p),
      { contradiction },
      { apply prf.ax, assumption } }
end

-- transitivity

lemma access.trans : ∀ w ∈ domain σ, ∀ v ∈ domain σ, ∀ u ∈ domain σ,
  access w v = tt → access v u = tt → access w u = tt :=
begin
  intros w hw v hv u hu, unfold access,
  simp, intros sw sv p hp,
  apply sv, apply mem_unbox_iff_mem_box.2,
  apply sw, apply mem_unbox_iff_mem_box.2,
  apply mem_domain_of_prf, assumption,
  apply prf.mp,
  { exact prf.s4 },
  { apply prf.ax,
    apply mem_unbox_iff_mem_box.1,
    assumption }
end

noncomputable def model : @model σ :=
begin
  fapply model.mk,
    apply domain,
    apply access,
    apply val,
    apply access.refl,
    apply access.symm,
    apply access.trans
end

/- truth is membership in the canonical model -/

lemma form_tt_iff_mem_wrld {p : form σ} : 
  ∀ (w ∈ domain σ), (w ⊩⦃model⦄ p) = tt ↔ p ∈ w :=
begin
  induction p with v p q hp hq p hp,
  { intros, unfold forces_form model val, simp,
    apply iff.intro,
    { intro h, exact h.right },
    { intro h, split, repeat {assumption} } },
  
  { unfold forces_form, simp,
    intros w wm h, apply mem_domain_consist wm (prf.ax h) },

  { unfold forces_form, simp, intros v wm, 
    apply iff.intro,
    { intro h, cases h, 
      { cases mem_domain_max wm p with h₁ h₂,
        { refine ctx.mem_max_of_prf wm _, 
          exact (prf.mp prf.pl1 (prf.ax ((hq _ wm).1 h))) },
        { refine ctx.mem_max_of_prf wm _, 
          apply prf.mp prf.contrap (prf.mp prf.pl1 (prf.ax h₂)) } },  
      { cases mem_domain_max wm q with h₁ h₂,
        { refine ctx.mem_max_of_prf wm _,
          exact prf.mp prf.pl1 (prf.ax h₁) },
        { refine ctx.mem_max_of_prf wm _,
          refine prf.mp prf.contrap (prf.mp prf.pl1 _),
          cases mem_domain_max wm p with hp₁ hp₂,
          { exfalso, apply ff_eq_tt_eq_false,
            transitivity, 
            { exact h.symm },
            { exact (hp _ wm).2 hp₁} },
          { apply prf.ax hp₂ } } } },
      { intro h,
        cases mem_domain_max wm q with h₁ h₂,
        { left, exact (hq _ wm).2 h₁ },
        { cases mem_domain_max wm p with hp₁ hp₂,
          { exfalso, apply mem_domain_consist wm,
            exact prf.mp (prf.ax h₂) (prf.mp (prf.ax h) (prf.ax hp₁)) },
          { right, apply eq_ff_of_not_eq_tt,
            intro ptt, apply mem_domain_consist wm,
            exact prf.mp (prf.ax hp₂) (prf.ax ((hp _ wm).1 ptt)) } } } },
  
  { unfold forces_form,
    simp, intros w wm,
    apply iff.intro,
    { intro h,
      cases mem_domain_max wm (◻p) with h₁ h₂,
      { exact h₁ },
        exfalso, apply ctx.is_consist_max (consist_unbox_of_not_box_mem wm h₂),
        apply prf.mp,
        { apply prf.ax (ctx.subset_max_self (mem_insert _ _)) },
        { apply prf.ax, 
          apply (hp _ (mem_domain (consist_unbox_of_not_box_mem wm h₂))).1,
          apply h, apply mem_domain (consist_unbox_of_not_box_mem wm h₂), exact wm,
          apply subset_unbox_iff_access.2,
          intros p pm, apply ctx.subset_max_self,
          apply mem_insert_of_mem _ pm } },
      
    { intro h,
      intros w v, unfold model access, simp, 
      intros wm' rwv, 
      exact (hp _ v).2 (rwv (mem_unbox_iff_mem_box.2 h)) } }
end

lemma ctx_tt_of_mem_domain (Γ : ctx σ) (wm : Γ ∈ domain σ) : 
  (Γ ⊩⦃model⦄ Γ) = tt :=
mem_tt_to_ctx_tt Γ (λ p pm, (form_tt_iff_mem_wrld _ wm).2 pm)

/- the completeness lemma -/

theorem completeness {Γ : ctx σ} {p : form σ} : 
  (Γ ⊨ₛ₅ p) → (Γ ⊢ₛ₅ p) :=
begin
  apply (@not_imp_not (Γ ⊢ₛ₅ p) (Γ ⊨ₛ₅ p) (prop_decidable _)).1,
  intros nhp hp, cases hp,
  have c : is_consist (Γ ⸴ ~p) := consist_not_of_not_prf nhp,
  apply absurd,
  fapply hp,
    { exact model },
    { exact ctx.max (Γ ⸴ ~p) },
    { apply mem_domain c },

    { apply cons_ctx_tt_to_ctx_tt,
      apply ctx_tt_to_subctx_tt,
      apply ctx_tt_of_mem_domain (ctx.max (Γ ⸴ ~p)),
      apply mem_domain c,
      apply ctx.subset_max_self },

    { simp, apply eq_ff_of_not_eq_tt,
      apply neg_tt_iff_ff.1, 
      apply and.elim_right,
      apply cons_ctx_tt_iff_and.1, 
      apply ctx_tt_to_subctx_tt,
      apply ctx_tt_of_mem_domain (ctx.max (Γ ⸴ ~p)),
      apply mem_domain c,
      apply ctx.subset_max_self },
end

end canonical