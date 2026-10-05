/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainHoleBudget

set_option autoImplicit false

/-!
# The posted hole-fraction residual is refutable, not open

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoPlainHoleBudget.lean`
reduces the Hole-Lemma budget of `[DuanWuZhou2022]` §6.2 to `Dwz63HoleFractionInputs`, and reports
it *open*: two cardinality inequalities that the hashing layer does not supply.  This module shows
that they are not open but **inconsistent**, so that no amount of hashing, and no passage to a
retained subset, can discharge them.  The obstruction is structural and is identified exactly.

## The one extra hypothesis, and where it comes from

Everything below is stated under

`hrefines : ∀ w b, usefulFor w b → compatibleWith w b`,

which is `[DuanWuZhou2022]`'s `def:useful_g` (`global_value.tex:76`) refining
`def:global-compatible`: a small block useful for a triple is in particular compatible with it.
Two places in the tree already carry it:

* `Combinatorics/CompatibleSplitCount.lean`'s
  `CompatibleSplit.SplitRequirements.mem_compatibleSet_of_mem_usefulSet` **proves** it for the
  committed `usefulSet`/`compatibleSet`;
* `Examples/DuanWuZhouLevelTwoPlainGroupedStage.lean`'s
  `dwz63_mem_plainGroupedZSupport_of_notMem_holes` **assumes** it, in this exact shape, as the
  premise `hrefines`.

So it is not an extra assumption about the intended instantiation; it *is* the intended
instantiation.

## The refutation

Two independent statements, both consequences of one covering fact.  Since
`{w | useful w b}` is contained in `{w | compatible w b}`, the useless words of `b` and the words
compatible with `b` **cover** every available word
(`card_le_card_dwz63UselessZWords_add_card_dwz63CompatibleZWords`).

* `card_eq_zero_of_dwz63HoleFractionInputs`.  For a **single** retained triple `a` the residual's
  own three conjuncts already collapse: the third bounds the useless words by `|avail|/16`, so the
  words compatible with `a` are at least `15|avail|/16`, so `shareBound ≥ 15|avail|/16`; but the
  second bounds `16 · #retained · shareBound` by `|avail|` and `#retained ≥ 1`.  Hence
  `|avail| = 0`.  `eq_empty_of_dwz63HoleFractionInputs` restates this as: on a nondegenerate
  alphabet the residual holds only on the **empty** retained family, and
  `dwz63HoleFractionInputs_empty_iff` records what is left there (rule (ii) alone).

* `fifteen_mul_card_le_sixteen_mul_card_dwz63HoleSet` and
  `card_eq_zero_of_eight_mul_card_dwz63HoleSet_le`.  The defect is not in `shareBound` but in
  `dwz63HoleSet` itself: as soon as **two** triples are retained and rule (ii)'s density holds for
  one of them, every hole set of another one already has at least a `15/16` fraction of the
  available words, so the `1/8` bound `claim:hole_frac_low` asks for is unreachable.  This version
  survives any re-aggregation of the residual (see `card_eq_zero_of_dwz63AggregateHoleFraction` in
  `Examples/DuanWuZhouLevelTwoAggregateHoleBudget.lean`), which is why it is stated separately.

## What is actually wrong, and what is not

Nothing above says the paper is wrong; it says the *binary* relation pair is.  In
`[DuanWuZhou2022]` the small blocks of the copy `(X_I, Y_J, Z_K)` are the available blocks **of
that copy**, and Step 2's competitor test is applied to a block *in its own copy's coordinates*.
The localized stage identifies every copy with one reference leaf through a position relabeling
(`Examples/DuanWuZhouLevelTwoLocalizedStage.lean`'s `dwz63_constituent_restricts_brokenReferenceLeaf`,
its `σ`), and under that identification the two rules pull back to relations that are **owner
relative**: rule (ii) is the diagonal `useful (σ_a w) a`, which is all of the reference available
set, while rule (i) is `compatible (σ_a w) b` for `b ≠ a`, which is a small part of it.  A single
binary `compatibleWith`/`usefulFor` pair on the shared reference alphabet cannot hold both at
once — that is precisely the contradiction proved here.

Consequently the repair is not a stronger hashing lemma but a change of shape: the hole family
must be carried as a *family*, `holes : retained → Finset (SegmentedAvailableWord seg α)`, exactly
as `Examples/DuanWuZhouLevelTwoLocalizedStage.lean` already carries it, and the budget must be
derived from a statement about that family.  That is done in
`Examples/DuanWuZhouLevelTwoAggregateHoleBudget.lean`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`, `def:useful_g`, `claim:hole_frac_low`) and
`hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

section Refutation

variable {I : Type u} [Fintype I] [DecidableEq I] {n m : ℕ}
variable {τ : Type v} [Fintype τ] [DecidableEq τ]

/-! ## The covering fact -/

omit [Fintype τ] [DecidableEq τ] in
/-- **Uselessness and compatibility cover the available words.**

`def:useful_g` refines compatibility, so a word that is not useless for `b` is compatible with
`b`.  This is the only place `hrefines` is used. -/
theorem card_le_card_dwz63UselessZWords_add_card_dwz63CompatibleZWords
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop)
    (hrefines : ∀ (w : SegmentedAvailableWord seg α) (b : τ), usefulFor w b → compatibleWith w b)
    (b : τ) :
    Fintype.card (SegmentedAvailableWord seg α) ≤
      (dwz63UselessZWords seg α usefulFor b).card +
        (dwz63CompatibleZWords seg α compatibleWith b).card := by
  classical
  have hcover : (Finset.univ : Finset (SegmentedAvailableWord seg α)) ⊆
      dwz63UselessZWords seg α usefulFor b ∪ dwz63CompatibleZWords seg α compatibleWith b := by
    intro w _
    by_cases hw : usefulFor w b
    · refine Finset.mem_union_right _ ?_
      simp only [dwz63CompatibleZWords, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hrefines w b hw
    · refine Finset.mem_union_left _ ?_
      simp only [dwz63UselessZWords, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hw
  calc Fintype.card (SegmentedAvailableWord seg α)
      = (Finset.univ : Finset (SegmentedAvailableWord seg α)).card := Finset.card_univ.symm
    _ ≤ (dwz63UselessZWords seg α usefulFor b ∪
          dwz63CompatibleZWords seg α compatibleWith b).card := Finset.card_le_card hcover
    _ ≤ (dwz63UselessZWords seg α usefulFor b).card +
          (dwz63CompatibleZWords seg α compatibleWith b).card := Finset.card_union_le _ _

/-- **The same cover, read through the hole set of another retained triple.**

If `b` is retained and different from `a`, every word compatible with `b` is a hole for `a` by
rule (i), so uselessness for `b` and the hole set of `a` already cover everything. -/
theorem card_le_card_dwz63UselessZWords_add_card_dwz63HoleSet
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) (retained : Finset τ)
    (compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop)
    (hrefines : ∀ (w : SegmentedAvailableWord seg α) (b : τ), usefulFor w b → compatibleWith w b)
    {a b : τ} (hb : b ∈ retained) (hba : b ≠ a) :
    Fintype.card (SegmentedAvailableWord seg α) ≤
      (dwz63UselessZWords seg α usefulFor b).card +
        (dwz63HoleSet seg α retained compatibleWith usefulFor a).card := by
  classical
  have hcover : (Finset.univ : Finset (SegmentedAvailableWord seg α)) ⊆
      dwz63UselessZWords seg α usefulFor b ∪
        dwz63HoleSet seg α retained compatibleWith usefulFor a := by
    intro w _
    by_cases hw : usefulFor w b
    · refine Finset.mem_union_right _ ?_
      rw [mem_dwz63HoleSet]
      exact Or.inl ⟨b, hb, hba, hrefines w b hw⟩
    · refine Finset.mem_union_left _ ?_
      simp only [dwz63UselessZWords, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hw
  calc Fintype.card (SegmentedAvailableWord seg α)
      = (Finset.univ : Finset (SegmentedAvailableWord seg α)).card := Finset.card_univ.symm
    _ ≤ (dwz63UselessZWords seg α usefulFor b ∪
          dwz63HoleSet seg α retained compatibleWith usefulFor a).card :=
        Finset.card_le_card hcover
    _ ≤ (dwz63UselessZWords seg α usefulFor b).card +
          (dwz63HoleSet seg α retained compatibleWith usefulFor a).card :=
        Finset.card_union_le _ _

/-! ## The residual is inconsistent -/

omit [Fintype τ] [DecidableEq τ] in
/-- **`Dwz63HoleFractionInputs` forces the available alphabet to be empty.**

One retained triple suffices.  The third conjunct makes the words compatible with it at least
`15/16` of the alphabet, hence `shareBound` at least that; the second conjunct makes
`16 · shareBound` at most the whole alphabet. -/
theorem card_eq_zero_of_dwz63HoleFractionInputs
    {seg : Fin (n + 1) → Fin m} {α : Fin m → I → ℕ} {retained : Finset τ}
    {compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop} {shareBound : ℕ}
    (hrefines : ∀ (w : SegmentedAvailableWord seg α) (b : τ), usefulFor w b → compatibleWith w b)
    (hinputs : Dwz63HoleFractionInputs seg α retained compatibleWith usefulFor shareBound)
    {a : τ} (ha : a ∈ retained) :
    Fintype.card (SegmentedAvailableWord seg α) = 0 := by
  obtain ⟨hshare, hunion, huseless⟩ := hinputs
  have hcover := card_le_card_dwz63UselessZWords_add_card_dwz63CompatibleZWords
    seg α compatibleWith usefulFor hrefines a
  have hcompat := hshare a ha
  have hcardpos : 0 < retained.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hmul : shareBound ≤ retained.card * shareBound :=
    Nat.le_mul_of_pos_left shareBound hcardpos
  have huse := huseless a
  omega

omit [Fintype τ] [DecidableEq τ] in
/-- **The residual cannot hold on a nonempty retained family.** -/
theorem not_dwz63HoleFractionInputs
    {seg : Fin (n + 1) → Fin m} {α : Fin m → I → ℕ} {retained : Finset τ}
    {compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop} {shareBound : ℕ}
    (hrefines : ∀ (w : SegmentedAvailableWord seg α) (b : τ), usefulFor w b → compatibleWith w b)
    (hpos : 0 < Fintype.card (SegmentedAvailableWord seg α))
    {a : τ} (ha : a ∈ retained) :
    ¬ Dwz63HoleFractionInputs seg α retained compatibleWith usefulFor shareBound := by
  intro hinputs
  have hzero := card_eq_zero_of_dwz63HoleFractionInputs hrefines hinputs ha
  omega

omit [Fintype τ] in
/-- **No retained subset carries the residual.**

The deliverable a hashing argument would have had to produce — a retained subset of positive
size on which `Dwz63HoleFractionInputs` holds — does not exist. -/
theorem eq_empty_of_dwz63HoleFractionInputs
    {seg : Fin (n + 1) → Fin m} {α : Fin m → I → ℕ} {retained : Finset τ}
    {compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop} {shareBound : ℕ}
    (hrefines : ∀ (w : SegmentedAvailableWord seg α) (b : τ), usefulFor w b → compatibleWith w b)
    (hpos : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (hinputs : Dwz63HoleFractionInputs seg α retained compatibleWith usefulFor shareBound) :
    retained = ∅ := by
  by_contra hne
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  exact not_dwz63HoleFractionInputs hrefines hpos ha hinputs

omit [Fintype τ] [DecidableEq τ] in
/-- **What survives on the empty family**: rule (ii) alone.  Together with
`eq_empty_of_dwz63HoleFractionInputs` this pins the residual exactly — it is satisfiable, but only
vacuously. -/
theorem dwz63HoleFractionInputs_empty_iff (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop) (shareBound : ℕ) :
    Dwz63HoleFractionInputs seg α (∅ : Finset τ) compatibleWith usefulFor shareBound ↔
      ∀ a : τ, 16 * (dwz63UselessZWords seg α usefulFor a).card ≤
        Fintype.card (SegmentedAvailableWord seg α) := by
  constructor
  · intro h
    exact h.2.2
  · intro h
    refine ⟨?_, ?_, h⟩
    · intro b hb
      exact absurd hb (Finset.notMem_empty b)
    · simp

/-! ## The defect is in the hole set, not in `shareBound` -/

/-- **Every hole set already contains a `15/16` fraction of the alphabet.**

`b` is any *other* retained triple whose useless words are sparse (rule (ii) for `b`).  This uses
neither `shareBound` nor the union bound, so it is unaffected by any restatement of the residual
that keeps `dwz63HoleSet` and a single binary compatibility relation. -/
theorem fifteen_mul_card_le_sixteen_mul_card_dwz63HoleSet
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) (retained : Finset τ)
    (compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop)
    (hrefines : ∀ (w : SegmentedAvailableWord seg α) (b : τ), usefulFor w b → compatibleWith w b)
    {a b : τ} (hb : b ∈ retained) (hba : b ≠ a)
    (huseless : 16 * (dwz63UselessZWords seg α usefulFor b).card ≤
      Fintype.card (SegmentedAvailableWord seg α)) :
    15 * Fintype.card (SegmentedAvailableWord seg α) ≤
      16 * (dwz63HoleSet seg α retained compatibleWith usefulFor a).card := by
  have hcover := card_le_card_dwz63UselessZWords_add_card_dwz63HoleSet
    seg α retained compatibleWith usefulFor hrefines hb hba
  omega

/-- **`claim:hole_frac_low` is unreachable in the binary shape.**  With two retained triples,
rule (ii) for one of them and the `1/8` hole bound for the other force `|avail| = 0`. -/
theorem card_eq_zero_of_eight_mul_card_dwz63HoleSet_le
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) (retained : Finset τ)
    (compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop)
    (hrefines : ∀ (w : SegmentedAvailableWord seg α) (b : τ), usefulFor w b → compatibleWith w b)
    {a b : τ} (hb : b ∈ retained) (hba : b ≠ a)
    (huseless : 16 * (dwz63UselessZWords seg α usefulFor b).card ≤
      Fintype.card (SegmentedAvailableWord seg α))
    (hholes : 8 * (dwz63HoleSet seg α retained compatibleWith usefulFor a).card ≤
      Fintype.card (SegmentedAvailableWord seg α)) :
    Fintype.card (SegmentedAvailableWord seg α) = 0 := by
  have hfifteen := fifteen_mul_card_le_sixteen_mul_card_dwz63HoleSet
    seg α retained compatibleWith usefulFor hrefines hb hba huseless
  omega

end Refutation

end AlgebraicComplexity.Examples
