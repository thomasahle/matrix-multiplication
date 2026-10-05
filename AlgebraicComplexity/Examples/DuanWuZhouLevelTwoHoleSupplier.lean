/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedHoleRepair
import AlgebraicComplexity.MatrixMultiplication.AsymmetricGlobalBudget

/-!
# The holes of `[DuanWuZhou2022]` Additional Zeroing-Out Step 2

Layer 4 (`AlgebraicComplexity/Examples/`).  `global_value.tex:74-89` zeroes a small `Z`-block
`Z_K̂` when either

* **(i)** it is compatible with **more than one** retained triple, or
* **(ii)** it is not **useful** (`def:useful_g`, `global_value.tex:76`) for the unique triple it is
  compatible with,

and the blocks so zeroed are exactly the *holes* of that triple's broken copy
(`def:broken_standard_form_tensor`, `hole_lemma.tex:48`).  `dwz63HoleSet` below is that `Finset`,
one per retained copy, in the `SegmentedAvailableWord` alphabet
`restricts_indexedDirectSum_segmentedHoleRepair_batched` consumes.

## Deliberately generic in the segmentation

The segmentation data (`seg`, the per-segment fine-`Z` profiles `α`) is the tensor lane's
`dwz63Seg`, still landing.  Nothing here needs its value: the two rules are statements about a
compatibility relation and a usefulness relation on available words, so this module is stated over
an arbitrary `(seg, α)` and an arbitrary retained index type.  When `dwz63Seg` lands it is
instantiated, not rewritten.

The fine `Z`-alphabet is `CWBlock`, the block index of `cwPartitionedTensor`
(`Examples/CoppersmithWinogradPartitionDataCore.lean:143-144`) --- the level-one Coppersmith--
Winograd partition, whose positive power the coarse square coarsens.  There is exactly one such
alphabet and this module does not introduce another.

## The budget

`claim:hole_frac_low` (`global_value.tex:251`) bounds the hole probability by `1/8`, i.e.
`8·|holes a| ≤ |available|`, and `AsymmetricGlobal.holeBudget_of_eight_mul_card_le`
(`MatrixMultiplication/AsymmetricGlobalBudget.lean:270`) is generic in the alphabet, so it applies
to `SegmentedAvailableWord` unchanged.  `dwz63_segmentedHoleBudget_batched` puts it in the exact
`∀ b : β` product shape the batched Hole Lemma asks for.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6 and `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v w

section Holes

variable {I : Type u} [Fintype I] [DecidableEq I] {n m : ℕ}
variable {τ : Type v} [Fintype τ] [DecidableEq τ]

/-- **The holes of one retained copy**, by `[DuanWuZhou2022]`'s two rules.

`compatibleWith w a` is "the small block `w` is compatible with the retained triple `a`" and
`usefulFor w a` is `def:useful_g`.  A block is a hole for `a` when it is compatible with some
*other* retained triple as well, or when it is compatible with `a` but not useful for it. -/
noncomputable def dwz63HoleSet (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (retained : Finset τ)
    (compatibleWith : SegmentedAvailableWord seg α → τ → Prop)
    (usefulFor : SegmentedAvailableWord seg α → τ → Prop)
    (a : τ) : Finset (SegmentedAvailableWord seg α) := by
  classical
  exact Finset.univ.filter fun w ↦
    (∃ b ∈ retained, b ≠ a ∧ compatibleWith w b) ∨ ¬ usefulFor w a

theorem mem_dwz63HoleSet {seg : Fin (n + 1) → Fin m} {α : Fin m → I → ℕ}
    {retained : Finset τ}
    {compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop}
    {a : τ} {w : SegmentedAvailableWord seg α} :
    w ∈ dwz63HoleSet seg α retained compatibleWith usefulFor a ↔
      (∃ b ∈ retained, b ≠ a ∧ compatibleWith w b) ∨ ¬ usefulFor w a := by
  classical
  simp [dwz63HoleSet]

/-- **A non-hole is useful and privately compatible.**  This is the positive reading of Step 2:
everything the rules keep is useful for `a` and compatible with no other retained triple, which is
what makes the surviving blocks of distinct triples disjoint despite the shared `Z`-blocks. -/
theorem usefulFor_of_notMem_dwz63HoleSet {seg : Fin (n + 1) → Fin m} {α : Fin m → I → ℕ}
    {retained : Finset τ}
    {compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop}
    {a : τ} {w : SegmentedAvailableWord seg α}
    (hw : w ∉ dwz63HoleSet seg α retained compatibleWith usefulFor a) :
    usefulFor w a ∧ ∀ b ∈ retained, b ≠ a → ¬ compatibleWith w b := by
  classical
  rw [mem_dwz63HoleSet] at hw
  push Not at hw
  exact ⟨hw.2, fun b hb hne ↦ hw.1 b hb hne⟩

/-! ## The Hole-Lemma budget in the segmented alphabet -/

/-- **`claim:hole_frac_low` in the shape the segmented Hole Lemma consumes.**

`AsymmetricGlobal.holeBudget_of_eight_mul_card_le` is generic in the alphabet, so the `1/8` hole
bound gives the product inequality over any finite index of copies. -/
theorem dwz63_segmentedHoleBudget (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) (L : ℕ)
    (hpos : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (hbound : Fintype.card (SegmentedAvailableWord seg α) ≤ 2 ^ L)
    {ι : Type w} [Fintype ι] (holes : ι → Finset (SegmentedAvailableWord seg α))
    (hholes : ∀ t, 8 * (holes t).card ≤ Fintype.card (SegmentedAvailableWord seg α))
    (hcopies : 8 * (L + 1) ≤ 7 * Fintype.card ι) :
    Fintype.card (SegmentedAvailableWord seg α) * ∏ t, (holes t).card <
      Fintype.card (SegmentedAvailableWord seg α) ^ Fintype.card ι :=
  AsymmetricGlobal.holeBudget_of_eight_mul_card_le holes L hpos hbound hholes hcopies

/-- **The batched budget**, in the exact `∀ b : β` shape of
`restricts_indexedDirectSum_segmentedHoleRepair_batched`'s `hbudget`.

The batching map is left abstract: any surjection with large enough fibers works, so a client may
use `uniformBatch` or its own. -/
theorem dwz63_segmentedHoleBudget_batched (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) (L : ℕ)
    (hpos : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (hbound : Fintype.card (SegmentedAvailableWord seg α) ≤ 2 ^ L)
    {retained : Type w} [Fintype retained] [DecidableEq retained]
    {β : Type w} [Fintype β] [DecidableEq β] (batch : retained → β)
    (holes : retained → Finset (SegmentedAvailableWord seg α))
    (hholes : ∀ t, 8 * (holes t).card ≤ Fintype.card (SegmentedAvailableWord seg α))
    (hcopies : ∀ b : β, 8 * (L + 1) ≤ 7 * Fintype.card {a : retained // batch a = b}) :
    ∀ b : β,
      Fintype.card (SegmentedAvailableWord seg α) *
          ∏ a : {a : retained // batch a = b}, (holes a.1).card <
        Fintype.card (SegmentedAvailableWord seg α) ^
          Fintype.card {a : retained // batch a = b} := by
  intro b
  exact dwz63_segmentedHoleBudget seg α L hpos hbound
    (fun a : {a : retained // batch a = b} ↦ holes a.1) (fun a ↦ hholes a.1) (hcopies b)

end Holes

end AlgebraicComplexity.Examples
