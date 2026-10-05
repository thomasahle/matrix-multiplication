/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSegmentationData

set_option autoImplicit false

/-!
# Why the fine `Z` alphabet must be the pair

Layer 4 (`AlgebraicComplexity/Examples/`).  This module is a **record of a design constraint**, not
part of the route.  It proves that a segmented split restriction over the single-block alphabet
`CWBlock` cannot express `[DuanWuZhou2022]`'s split `alphatilde`, which is why the fine alphabet in
`Examples/DuanWuZhouLevelTwoSegmentationData.lean` is `PositiveWord CWBlock 1` --- the ordered
**pair** of base blocks, `hole_lemma.tex:40`'s `(K̂_{2s-1}, K̂_{2s})`.

## The constraint

`alphatilde_{i,j,k}` is a distribution over `k_l`, the left `Z` digit of the split `k = k_l + k_r`
(`DESIGN_NOTE_ZSIDE_PAPER.md` §(c), `global_value.tex:146`).  The coarse digit is constant on a
cell, so `k_r` is determined by `k_l` and pinning the left-digit distribution pins the pair.

Under the **pair** alphabet one fine letter *is* the pair, so a per-segment profile
`Fin 15 → PositiveWord CWBlock 1 → ℕ` pins it directly.  Under the single-block alphabet a coarse
position contributes two letters to the same segment, so a per-segment profile sees only their
pooled marginal, and at `k = 2` that marginal is

`(pooled zero, pooled middle, pooled last) = (p_0 + p_2, 2 p_1, p_0 + p_2)`,

which fixes `p_1` and `p_0 + p_2` but **never separates `p_0` from `p_2`**.
`pooled_segmentMultiplicity_does_not_determine_left_digit` is that separation failure, exhibited on
two concrete two-position words.  The cells where the split is nontrivial --- `(0,2,2)`, `(2,0,2)`,
`(1,1,2)`, `(1,2,1)`, `(2,1,1)` --- all have `k = 2`, so they are exactly the rows the single-block
alphabet cannot carry.

## History

An intermediate convention used the `CWBlock` alphabet with `2(n+1)` positions, and a `Fin 30`
parity refinement was proposed here to repair it by separating left from right positions.  That
repair worked but was unnecessary: the committed bridge
(`Examples/DuanWuZhouLevelTwoFineExpansion.lean`, from
`Tensor/LocalizedCoarsenedSelection.lean:680`) already produces fine words over
`PositiveWord CWBlock 1`, because the fine partition is `(cwPartitionedTensor K q).positivePower 1`.
The parity definitions have therefore been **removed** from this module rather than left as a trap
for a reader who might take them for the live convention; only the obstruction theorem remains, and
it is what justifies the pair alphabet.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

/-! ## The obstruction, as a finite fact -/

/-- The two-coarse-position word whose left digits are all `zero`. -/
def dwz63LeftZeroWord : Fin 4 → CWBlock :=
  ![CWBlock.zero, CWBlock.last, CWBlock.zero, CWBlock.last]

/-- The two-coarse-position word whose left digits are all `last`. -/
def dwz63LeftLastWord : Fin 4 → CWBlock :=
  ![CWBlock.last, CWBlock.zero, CWBlock.last, CWBlock.zero]

/-- One segment: the pooled labelling a single-block segmentation induces on one cell. -/
def dwz63PooledSeg : Fin 4 → Fin 1 := fun _ ↦ 0

/-- Two segments: a parity labelling, separating left from right fine positions. -/
def dwz63ParitySeg : Fin 4 → Fin 2 := fun i ↦ ⟨i.val % 2, by omega⟩

/-- **The single-block alphabet cannot carry `alphatilde`.**

Two words over one `k = 2` cell whose **pooled** segment profile agrees at every `CWBlock` but
whose **left-digit** segment profile does not.  A segmented split restriction over `CWBlock`
constrains exactly the pooled profile, so it cannot express the split at any cell where the split
is nontrivial.  No choice of numbers repairs this; the alphabet has to be the pair.

Stated on `segmentMultiplicity` because that is what the segmented machinery reads --- and because
`WordType.multiplicity` is defined through `classical`, so `decide` cannot reduce it. -/
theorem pooled_segmentMultiplicity_does_not_determine_left_digit :
    (∀ b : CWBlock,
        segmentMultiplicity dwz63PooledSeg dwz63LeftZeroWord 0 b =
          segmentMultiplicity dwz63PooledSeg dwz63LeftLastWord 0 b) ∧
      ¬ (∀ b : CWBlock,
        segmentMultiplicity dwz63ParitySeg dwz63LeftZeroWord 0 b =
          segmentMultiplicity dwz63ParitySeg dwz63LeftLastWord 0 b) := by
  constructor
  · decide +kernel
  · decide +kernel

end AlgebraicComplexity.Examples
