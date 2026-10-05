/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetCounting
import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordQuotient

set_option autoImplicit false

/-!
# Nested total-weight labels for level-four CW words

A level-four Coppersmith--Winograd parent block has two labelled depth-two children, and each
depth-two child has two consecutive depth-one children.  This module records the four depth-one
total weights without forgetting which adjacent pair belongs to each depth-two child.  Summing an
adjacent pair recovers exactly the existing depth-two total-weight owner used by recursive hashing.

The construction follows the level-`lvl` consecutive-block convention and Definition
`def:split-hatI` of [alman2025more],
`papers/sources/2404.16349/prelim.tex:225-232,249-269`.  Its use at level-two quotient granularity
is Remark `rem:granularity-forced` of the Total-Weight manuscript,
`better_bound/paper.tex:1783-1800`.  The module contains only the structural coarsening and its
compatibility with the committed recursive outer address.  It does not define a hash model, an
evaluator cache, a support theorem, or a quotient-count bound.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*, Preliminaries,
  subsections “Leveled Partition for Large Tensor Powers” and “Complete Split
  Distributions,” Definition `def:split-hatI`.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*,
  Remark `rem:granularity-forced`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-! ## One depth-two child -/

/-- The two ordered depth-one total weights inside one depth-two child.

The two positions are the consecutive left and right halves supplied by `splitWordSuccEquiv 1`.
Each entry lies in `CWCoarseDigit 1 = Fin 5`. -/
abbrev CWDepthTwoTotalWeightPayload := Fin 2 → CWCoarseDigit 1

namespace CWDepthTwoTotalWeightPayload

/-- Recover the depth-two outer total by adding the two depth-one totals.

The sum lies in `CWRecursiveChildDigit 2 = Fin 9` because each input digit is at most four. -/
def outer (payload : CWDepthTwoTotalWeightPayload) : CWRecursiveChildDigit 2 :=
  ⟨(payload 0 : ℕ) + (payload 1 : ℕ), Nat.lt_succ_iff.mpr (by
    have hleft : (payload 0 : ℕ) ≤ coarseTotal 1 :=
      Nat.lt_succ_iff.mp (payload 0).isLt
    have hright : (payload 1 : ℕ) ≤ coarseTotal 1 :=
      Nat.lt_succ_iff.mp (payload 1).isLt
    calc
      (payload 0 : ℕ) + (payload 1 : ℕ) ≤
          coarseTotal 1 + coarseTotal 1 := Nat.add_le_add hleft hright
      _ = coarseTotal 2 := rfl)⟩

end CWDepthTwoTotalWeightPayload

/-- Read the two depth-one total weights inside a depth-two complete-split word. -/
def cwDepthTwoTotalWeightPayload (word : SplitWord 2) :
    CWDepthTwoTotalWeightPayload :=
  let children := splitWordSuccEquiv 1 word
  ![(cwSplitWordTotalMap 1).label children.1,
    (cwSplitWordTotalMap 1).label children.2]

/-- Adding the two nested totals gives the ordinary total of the depth-two word.

Proof sketch: `splitWordWeight_succ` partitions the four ternary positions into the same two
consecutive halves used by `cwDepthTwoTotalWeightPayload`; the quotient labels are their literal
digit sums. -/
@[simp] theorem cwDepthTwoTotalWeightPayload_outer (word : SplitWord 2) :
    (cwDepthTwoTotalWeightPayload word).outer = cwSplitWordTotalDigit 2 word := by
  apply Fin.ext
  change
    splitWordWeight (splitWordSuccEquiv 1 word).1 +
        splitWordWeight (splitWordSuccEquiv 1 word).2 =
      splitWordWeight word
  exact (splitWordWeight_succ 1 word).symm

/-! ## The whole level-four row -/

/-- A nested coordinate first selects one of the doubled depth-two child occurrences and then
one of that occurrence's two ordered depth-one children. -/
abbrev CWLevelFourNestedTotalWeightIndex (n : ℕ) :=
  Fin ((n + 1) + (n + 1)) × Fin 2

/-- The four-per-parent level-two quotient word, represented on the exact nested address type. -/
abbrev CWLevelFourNestedTotalWeightWord (n : ℕ) :=
  CWLevelFourNestedTotalWeightIndex n → CWCoarseDigit 1

/-- A three-leg address of nested level-two total-weight words. -/
abbrev CWLevelFourNestedTotalWeightAddress (n : ℕ) :=
  BlockAddress (fun _c ↦ CWLevelFourNestedTotalWeightWord n)

/-- Refine a word of level-four parent chunks by the two depth-one totals inside each of its
doubled depth-two child occurrences. -/
def cwLevelFourNestedTotalWeightWord (n : ℕ)
    (word : PositiveWord (PositiveWord CWBlock (2 ^ (2 + 1) - 1)) n) :
    CWLevelFourNestedTotalWeightWord n :=
  fun index ↦
    cwDepthTwoTotalWeightPayload
      (positiveWordLabelledChildren (cwChunkSplitWord (2 + 1)) word index.1) index.2

/-- Apply the nested total-weight refinement independently on all three physical legs. -/
def cwLevelFourNestedTotalWeightCoarsening (n : ℕ) :
    ∀ _c : Leg,
      PositiveWord (PositiveWord CWBlock (2 ^ (2 + 1) - 1)) n →
        CWLevelFourNestedTotalWeightWord n :=
  fun _c ↦ cwLevelFourNestedTotalWeightWord n

/-- Forget the inner pair boundary of a nested word by summing each adjacent depth-one pair. -/
def cwLevelFourNestedOuterWord (n : ℕ)
    (word : CWLevelFourNestedTotalWeightWord n) :
    Fin ((n + 1) + (n + 1)) → CWRecursiveChildDigit 2 :=
  fun occurrence ↦
    CWDepthTwoTotalWeightPayload.outer (fun side ↦ word (occurrence, side))

/-- Forget the nested payload on all three legs of a level-four address. -/
def cwLevelFourNestedOuterAddress (n : ℕ)
    (address : CWLevelFourNestedTotalWeightAddress n) :
    CWRecursiveCoarseAddress 2 n :=
  coarsenBlockAddress (fun _c ↦ cwLevelFourNestedOuterWord n) address

/-- Refining a level-four word and then forgetting the payload recovers its committed recursive
depth-two total-weight word.

Proof sketch: at each labelled child occurrence, the payload theorem recombines the two
depth-one halves into the full split-word weight.  The existing recursive child word stores that
same weight, as stated by `val_cwRecursiveLabelledChildWord_eq_splitWordWeight`. -/
@[simp] theorem cwLevelFourNestedOuterWord_map (n : ℕ)
    (word : PositiveWord (PositiveWord CWBlock (2 ^ (2 + 1) - 1)) n) :
    cwLevelFourNestedOuterWord n (cwLevelFourNestedTotalWeightWord n word) =
      cwRecursiveLabelledChildWord 2 n word := by
  funext occurrence
  change
    (cwDepthTwoTotalWeightPayload
        (positiveWordLabelledChildren
          (cwChunkSplitWord (2 + 1)) word occurrence)).outer =
      cwRecursiveLabelledChildWord 2 n word occurrence
  rw [cwDepthTwoTotalWeightPayload_outer]
  apply Fin.ext
  exact (val_cwRecursiveLabelledChildWord_eq_splitWordWeight
    2 n word occurrence).symm

/-- Address-level compatibility: nested coarsening followed by outer projection is exactly the
existing recursive child-group coarsening.

Proof sketch: addresses are functions of the physical leg, so the statement follows pointwise
from `cwLevelFourNestedOuterWord_map`. -/
@[simp] theorem cwLevelFourNestedOuterAddress_coarsen (n : ℕ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (2 + 1) - 1)) n)) :
    cwLevelFourNestedOuterAddress n
        (coarsenBlockAddress (cwLevelFourNestedTotalWeightCoarsening n) address) =
      cwRecursiveChildGroup 2 n address := by
  funext physicalLeg
  exact cwLevelFourNestedOuterWord_map n (address physicalLeg)

end AlgebraicComplexity.Examples
