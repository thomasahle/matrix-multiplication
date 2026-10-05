/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112TypedRestrictionPower

set_option autoImplicit false

/-!
# Transporting a word type along the `112` block dictionary

Layer 4 (`AlgebraicComplexity/Examples/`).  This is the letter- and word-level half of the
identification of `[duan2023faster]`'s `(1,1,2)` orbit region with a typed cut of the `112`
partition: the `alphatilde` row's support inside the cell, the collapse of the dictionary fibre
sum, the two-way transport of a word's multiplicity type along the dictionary, and the reading of
a one-segment split restriction as a plain word type.  The cell data, the two cut supports and the
restriction itself are in
`Examples/CoppersmithWinograd112TypedRestrictionCut.lean`, which imports this module.

## The paper step these results serve

`[duan2023faster]`, proof of `lem:non-rot-values` (d),
`papers/sources/2210.10173/second_power_appendix.tex:26-45`, especially the single long line `:37`:
the tensor `\T` is obtained from `T_{1,1,2}^{⊗m}` by zeroing out the blocks inconsistent with the
marginal distributions of `α^{(1,1,2)}`, and is a subtensor of
`T_{1,1,2}^{⊗m}[α̃_Z^{(1,1,2)}]`. The `Z`-marginal split `α̃_Z^{(1,1,2)}` is `eq:tilde_A`
(`second_power.tex:142-158`, statement `:145-156`); at level two it carries the free parameter `b`
of `global_value.tex:341-348`.  The optimisation of that split is Coppersmith and Winograd's value
of `T_{1,1,2}`, `[coppersmith1990matrix]`, pp. 270--272.

The results below are **reusable Lean infrastructure**, not published claims: the paper writes the
zeroing-out and the type condition in one breath, whereas a partitioned formalization has to move
a multiplicity type across a change of block alphabet in both directions.  These theorems are that
transport.

Primary sources: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via
Asymmetric Hashing*, `[duan2023faster]`, `second_power_appendix.tex:26-45` (line `:37`),
`second_power.tex:142-158`, `global_value.tex:341-348`; Don Coppersmith and Shmuel Winograd,
*Matrix Multiplication via Arithmetic Progressions*, `[coppersmith1990matrix]`, pp. 270--272.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u w

/-! ## The `(1,1,2)` row is supported inside the cell -/

/-- The first orbit row of `dwz63OrbitRow` is `dwz63Alpha`'s row `6`, the `(1,1,2)` cell. -/
theorem dwz63_orbitRow_zero : dwz63OrbitRow 0 = 6 := rfl

/-- **The `(1,1,2)` split row vanishes off the cell.**  Contrapositive of
`dwz63_alphaTildeDegree_six`: a letter with nonzero `alphatilde` weight has coarse degree `2`,
which on the `Z` leg is exactly the `(1,1,2)` cell condition. -/
theorem dwz63_alphaTildeSix_eq_zero_of_not_cell (a : PositiveWord CWBlock 1)
    (ha : ¬ cw112RawCellKeep Leg.Z a) : dwz63AlphaTilde 6 a = 0 := by
  by_contra h
  exact ha (dwz63_alphaTildeDegree_six a h)

/-- The scaled row vanishes off the cell as well. -/
theorem dwz63_proportionalCountsSix_eq_zero_of_not_cell (j : ℕ) (a : PositiveWord CWBlock 1)
    (ha : ¬ cw112RawCellKeep Leg.Z a) :
    WordType.proportionalCounts (dwz63AlphaTilde 6) j a = 0 := by
  show dwz63AlphaTilde 6 a * j = 0
  rw [dwz63_alphaTildeSix_eq_zero_of_not_cell a ha, Nat.zero_mul]

/-! ## The dictionary fibre sum -/

/-- **The dictionary fibre sum collapses to the inverse-dictionary letter.**

`WordType.mappedType` sums a profile over the fibre of the block dictionary.  For a profile
supported inside the `(1,1,2)` cell exactly one fibre member contributes — the inverse-dictionary
letter `cw112RawDictInv Leg.Z b` — because any other cell letter in the fibre would be sent to the
same block, contradicting `cw112RawDictInv_dict`.

Proof sketch: `Finset.sum_eq_single_of_mem` at `cw112RawDictInv Leg.Z b`, which lies in the fibre
by `cw112RawDict_dictInv`; a different fibre member cannot satisfy the cell condition, since the
inverse round-trip would identify it with the singled-out letter, so the profile vanishes there.
The fibre sum runs over `PositiveWord CWBlock 1`, whose `Fintype` instance is noncomputable, so it
is singled out rather than enumerated. -/
theorem cw112RawDict_mappedType_apply (α : PositiveWord CWBlock 1 → ℕ)
    (hα : ∀ a, ¬ cw112RawCellKeep Leg.Z a → α a = 0) (b : CW112Block Leg.Z) :
    WordType.mappedType (cw112RawDict Leg.Z) α b = α (cw112RawDictInv Leg.Z b) := by
  show ∑ x ∈ WordType.letterFiber (cw112RawDict Leg.Z) b, α x = _
  refine Finset.sum_eq_single_of_mem (cw112RawDictInv Leg.Z b)
    (WordType.mem_letterFiber.mpr (cw112RawDict_dictInv Leg.Z b)) ?_
  intro x hx hne
  refine hα x fun hcell ↦ hne ?_
  have hxb : cw112RawDict Leg.Z x = b := WordType.mem_letterFiber.mp hx
  calc x = cw112RawDictInv Leg.Z (cw112RawDict Leg.Z x) :=
        (cw112RawDictInv_dict Leg.Z x hcell).symm
    _ = cw112RawDictInv Leg.Z b := by rw [hxb]

/-- At a cell letter, the pushed-forward profile has the letter's own weight. -/
theorem cw112RawDict_mappedType_dict (α : PositiveWord CWBlock 1 → ℕ)
    (hα : ∀ a, ¬ cw112RawCellKeep Leg.Z a → α a = 0)
    (a : PositiveWord CWBlock 1) (ha : cw112RawCellKeep Leg.Z a) :
    WordType.mappedType (cw112RawDict Leg.Z) α (cw112RawDict Leg.Z a) = α a := by
  rw [cw112RawDict_mappedType_apply α hα, cw112RawDictInv_dict Leg.Z a ha]

/-- **The pushforward is injective on profiles supported inside the cell.**  This is the backward
half of the type transport, and it is what makes the support hypothesis of
`Tensor.Restricts.partitionedBlockMap` — an *equality* — provable. -/
theorem cw112RawDict_mappedType_injOn (α β : PositiveWord CWBlock 1 → ℕ)
    (hα : ∀ a, ¬ cw112RawCellKeep Leg.Z a → α a = 0)
    (hβ : ∀ a, ¬ cw112RawCellKeep Leg.Z a → β a = 0)
    (h : WordType.mappedType (cw112RawDict Leg.Z) α =
      WordType.mappedType (cw112RawDict Leg.Z) β) : α = β := by
  funext a
  by_cases ha : cw112RawCellKeep Leg.Z a
  · rw [← cw112RawDict_mappedType_dict α hα a ha,
      ← cw112RawDict_mappedType_dict β hβ a ha, h]
  · rw [hα a ha, hβ a ha]

/-! ## Transporting a word type along the dictionary -/

/-- A word all of whose letters lie in the cell has a multiplicity type supported in the cell. -/
theorem cw112_multiplicity_eq_zero_of_not_cell {n : ℕ}
    (word : PositiveWord (PositiveWord CWBlock 1) n)
    (hword : ∀ i, cw112RawCellKeep Leg.Z
      (positiveWordEquiv (PositiveWord CWBlock 1) n word i))
    (a : PositiveWord CWBlock 1) (ha : ¬ cw112RawCellKeep Leg.Z a) :
    WordType.multiplicity (positiveWordEquiv (PositiveWord CWBlock 1) n word) a = 0 := by
  rw [WordType.multiplicity_eq_card_fiber]
  refine Fintype.card_eq_zero_iff.mpr ⟨fun i ↦ ?_⟩
  exact ha (i.2 ▸ hword i.1)

/-- **The forward half of the type transport.**  Mapping a word letterwise pushes its multiplicity
type forward along the dictionary; no hypothesis on the letters is needed. -/
theorem cw112_multiplicity_positiveWordMap_Z (n : ℕ)
    (word : PositiveWord (PositiveWord CWBlock 1) n) :
    WordType.multiplicity
        (positiveWordEquiv (CW112Block Leg.Z) n
          (positiveWordMap (cw112RawDict Leg.Z) n word)) =
      WordType.mappedType (cw112RawDict Leg.Z)
        (WordType.multiplicity (positiveWordEquiv (PositiveWord CWBlock 1) n word)) := by
  rw [positiveWordEquiv_map, WordType.multiplicity_comp_eq_mappedType]

/-- **The elementary two-way form of the type transport**: a cell letter occurs in a cell word
exactly as often as its dictionary image occurs in the dictionary image of the word. -/
theorem cw112_multiplicity_apply_dict {n : ℕ}
    (word : PositiveWord (PositiveWord CWBlock 1) n)
    (hword : ∀ i, cw112RawCellKeep Leg.Z
      (positiveWordEquiv (PositiveWord CWBlock 1) n word i))
    (a : PositiveWord CWBlock 1) (ha : cw112RawCellKeep Leg.Z a) :
    WordType.multiplicity
        (positiveWordEquiv (CW112Block Leg.Z) n
          (positiveWordMap (cw112RawDict Leg.Z) n word)) (cw112RawDict Leg.Z a) =
      WordType.multiplicity (positiveWordEquiv (PositiveWord CWBlock 1) n word) a := by
  rw [cw112_multiplicity_positiveWordMap_Z]
  exact cw112RawDict_mappedType_dict _
    (cw112_multiplicity_eq_zero_of_not_cell word hword) a ha

/-! ## A one-segment profile is a plain word type -/

/-- On the constrained leg, a segmented restriction carried on the single segment `t₀` is the
plain word-type condition. -/
theorem dwz63_keeps_constSeg_iff {A : Leg → Type w} [∀ c, DecidableEq (A c)]
    {M : ℕ} (t₀ : Fin M) (α : A Leg.Z → ℕ) (n : ℕ) (word : PositiveWord (A Leg.Z) n) :
    (SegmentedSplitRestriction.ofLeg (A := A) Leg.Z
        (fun t ↦ if t = t₀ then α else 0)).Keeps n (fun _ ↦ t₀) Leg.Z word ↔
      WordType.multiplicity (positiveWordEquiv (A Leg.Z) n word) = α := by
  rw [SegmentedSplitRestriction.keeps_iff_of_some
    (fun t ↦ SegmentedSplitRestriction.ofLeg_self (A := A) Leg.Z _ t)]
  constructor
  · intro h
    have ht := h t₀
    rw [dwz63_segmentMultiplicity_constSeg] at ht
    simpa using ht
  · intro h t
    rw [dwz63_segmentMultiplicity_constSeg]
    by_cases hts : t = t₀
    · simp [hts, h]
    · simp [hts]

/-- Off the constrained leg a `SegmentedSplitRestriction.ofLeg` restriction keeps every word. -/
theorem dwz63_keeps_constSeg_of_ne {A : Leg → Type w} [∀ c, DecidableEq (A c)]
    {M n : ℕ} {c : Leg} (hc : Leg.Z ≠ c) (β : Fin M → A Leg.Z → ℕ)
    (seg : Fin (n + 1) → Fin M) (word : PositiveWord (A c) n) :
    (SegmentedSplitRestriction.ofLeg (A := A) Leg.Z β).Keeps n seg c word :=
  SegmentedSplitRestriction.keeps_of_all_none
    (fun t ↦ SegmentedSplitRestriction.ofLeg_of_ne β hc t) word

end AlgebraicComplexity.Examples
