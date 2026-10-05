/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112TypedRestrictionCut

set_option autoImplicit false

/-!
# The `112` word-type transport, on an arbitrary leg

Layer 4 (`AlgebraicComplexity/Examples/`).
`Examples/CoppersmithWinograd112TypedRestrictionTransport.lean` transports a word type along the
`112` block dictionary on the `Z` leg, which is the leg the `(1,1,2)` component's `alphatilde` row
constrains.  The two rotated orbit rows of `[duan2023faster]`'s level-two fine leaf --- `(1,2,1)`
and `(2,1,1)`, after the rotation of
`Examples/DuanWuZhouLevelTwoOrbitRotatedRegion.lean` --- constrain the `X` resp. `Y` leg of the
*same* `(1,1,2)` cell instead.  This module restates the transport with the constrained leg as a
parameter; the proofs are the `Z` ones with `Leg.Z` replaced by `c₀`, since the letter dictionary
`cw112RawDict` and its inverse are already leg-indexed.

## The paper step these results serve

`[duan2023faster]`, proof of `lem:non-rot-values` (d),
`papers/sources/2210.10173/second_power_appendix.tex:26-45`, especially line `:37`: the tensor `\T`
is obtained from `T_{1,1,2}^{⊗m}` by zeroing out the blocks inconsistent with the marginal
distributions, and is a subtensor of `T_{1,1,2}^{⊗m}[α̃^{(1,1,2)}]`.  For the two rotated rows
the constrained marginal is the one the rotation moved, `second_power.tex:142-158` read through
`second_power.tex:235` (`note:T112`); the level-two split is the symmetric degree-one one of
`global_value.tex:347`.

The results below are **reusable Lean infrastructure**, not published claims: a partitioned
formalization has to move a multiplicity type across a change of block alphabet in both
directions, and the paper writes the zeroing-out and the type condition in one breath.

Primary sources: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via
Asymmetric Hashing*, `[duan2023faster]`, `second_power_appendix.tex:26-45` (line `:37`),
`second_power.tex:142-158`, `:235`, `global_value.tex:341-348` (`:347`); Don Coppersmith and
Shmuel Winograd, *Matrix Multiplication via Arithmetic Progressions*, `[coppersmith1990matrix]`,
pp. 270--272.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u w

/-! ## The dictionary fibre sum, on an arbitrary leg -/

/-- **The dictionary fibre sum collapses to the inverse-dictionary letter**, on any leg.

Proof sketch: `Finset.sum_eq_single_of_mem` at `cw112RawDictInv c₀ b`, which lies in the fibre by
`cw112RawDict_dictInv`; a different fibre member cannot satisfy the cell condition, since the
inverse round-trip would identify it with the singled-out letter, so the profile vanishes there. -/
theorem cw112RawDict_mappedTypeAt_apply (c₀ : Leg) (α : PositiveWord CWBlock 1 → ℕ)
    (hα : ∀ a, ¬ cw112RawCellKeep c₀ a → α a = 0) (b : CW112Block c₀) :
    WordType.mappedType (cw112RawDict c₀) α b = α (cw112RawDictInv c₀ b) := by
  show ∑ x ∈ WordType.letterFiber (cw112RawDict c₀) b, α x = _
  refine Finset.sum_eq_single_of_mem (cw112RawDictInv c₀ b)
    (WordType.mem_letterFiber.mpr (cw112RawDict_dictInv c₀ b)) ?_
  intro x hx hne
  refine hα x fun hcell ↦ hne ?_
  have hxb : cw112RawDict c₀ x = b := WordType.mem_letterFiber.mp hx
  calc x = cw112RawDictInv c₀ (cw112RawDict c₀ x) :=
        (cw112RawDictInv_dict c₀ x hcell).symm
    _ = cw112RawDictInv c₀ b := by rw [hxb]

/-- At a cell letter, the pushed-forward profile has the letter's own weight. -/
theorem cw112RawDict_mappedTypeAt_dict (c₀ : Leg) (α : PositiveWord CWBlock 1 → ℕ)
    (hα : ∀ a, ¬ cw112RawCellKeep c₀ a → α a = 0)
    (a : PositiveWord CWBlock 1) (ha : cw112RawCellKeep c₀ a) :
    WordType.mappedType (cw112RawDict c₀) α (cw112RawDict c₀ a) = α a := by
  rw [cw112RawDict_mappedTypeAt_apply c₀ α hα, cw112RawDictInv_dict c₀ a ha]

/-- **The pushforward is injective on profiles supported inside the cell**, on any leg. -/
theorem cw112RawDict_mappedTypeAt_injOn (c₀ : Leg) (α β : PositiveWord CWBlock 1 → ℕ)
    (hα : ∀ a, ¬ cw112RawCellKeep c₀ a → α a = 0)
    (hβ : ∀ a, ¬ cw112RawCellKeep c₀ a → β a = 0)
    (h : WordType.mappedType (cw112RawDict c₀) α =
      WordType.mappedType (cw112RawDict c₀) β) : α = β := by
  funext a
  by_cases ha : cw112RawCellKeep c₀ a
  · rw [← cw112RawDict_mappedTypeAt_dict c₀ α hα a ha,
      ← cw112RawDict_mappedTypeAt_dict c₀ β hβ a ha, h]
  · rw [hα a ha, hβ a ha]

/-! ## Transporting a word type along the dictionary, on an arbitrary leg -/

/-- A word all of whose letters lie in the cell has a multiplicity type supported in the cell. -/
theorem cw112_multiplicityAt_eq_zero_of_not_cell (c₀ : Leg) {n : ℕ}
    (word : PositiveWord (PositiveWord CWBlock 1) n)
    (hword : ∀ i, cw112RawCellKeep c₀
      (positiveWordEquiv (PositiveWord CWBlock 1) n word i))
    (a : PositiveWord CWBlock 1) (ha : ¬ cw112RawCellKeep c₀ a) :
    WordType.multiplicity (positiveWordEquiv (PositiveWord CWBlock 1) n word) a = 0 := by
  rw [WordType.multiplicity_eq_card_fiber]
  refine Fintype.card_eq_zero_iff.mpr ⟨fun i ↦ ?_⟩
  exact ha (i.2 ▸ hword i.1)

/-- **The forward half of the type transport**, on any leg: mapping a word letterwise pushes its
multiplicity type forward along the dictionary. -/
theorem cw112_multiplicity_positiveWordMapAt (c₀ : Leg) (n : ℕ)
    (word : PositiveWord (PositiveWord CWBlock 1) n) :
    WordType.multiplicity
        (positiveWordEquiv (CW112Block c₀) n
          (positiveWordMap (cw112RawDict c₀) n word)) =
      WordType.mappedType (cw112RawDict c₀)
        (WordType.multiplicity (positiveWordEquiv (PositiveWord CWBlock 1) n word)) := by
  rw [positiveWordEquiv_map, WordType.multiplicity_comp_eq_mappedType]

/-! ## A one-segment profile is a plain word type, on an arbitrary leg -/

/-- On the constrained leg, a segmented restriction carried on the single segment `t₀` is the
plain word-type condition. -/
theorem dwz63_keepsAt_constSeg_iff {A : Leg → Type w} [∀ c, DecidableEq (A c)]
    {M : ℕ} (c₀ : Leg) (t₀ : Fin M) (α : A c₀ → ℕ) (n : ℕ)
    (word : PositiveWord (A c₀) n) :
    (SegmentedSplitRestriction.ofLeg (A := A) c₀
        (fun t ↦ if t = t₀ then α else 0)).Keeps n (fun _ ↦ t₀) c₀ word ↔
      WordType.multiplicity (positiveWordEquiv (A c₀) n word) = α := by
  rw [SegmentedSplitRestriction.keeps_iff_of_some
    (fun t ↦ SegmentedSplitRestriction.ofLeg_self (A := A) c₀ _ t)]
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
theorem dwz63_keepsAt_constSeg_of_ne {A : Leg → Type w} [∀ c, DecidableEq (A c)]
    {M n : ℕ} {c₀ c : Leg} (hc : c₀ ≠ c) (β : Fin M → A c₀ → ℕ)
    (seg : Fin (n + 1) → Fin M) (word : PositiveWord (A c) n) :
    (SegmentedSplitRestriction.ofLeg (A := A) c₀ β).Keeps n seg c word :=
  SegmentedSplitRestriction.keeps_of_all_none
    (fun t ↦ SegmentedSplitRestriction.ofLeg_of_ne β hc t) word

end AlgebraicComplexity.Examples
