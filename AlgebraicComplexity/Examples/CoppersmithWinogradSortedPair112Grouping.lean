/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPair112Residual
import AlgebraicComplexity.Tensor.PositivePowerCoarseningFiberRestriction

set_option autoImplicit false

/-!
# Whole-group powers of the sorted-pair CW `(112)` residual

The accepted sorted-pair residual is a cut to two quotient addresses.  On that cut the X and Y
labels are already the single label `01`, while the Z label is either `02` or `11`.  This client
coarsens every remaining label to `Unit`; relative to the cut, this is exactly the operation that
keeps the two Z addresses together as one complete group.

The construction is the finite algebraic grouping step in the exceptional `(1,1,2)` argument of
[CoppersmithWinograd1990, pp. 270--272], transcribed in
`papers/notes/MMult1987.tex:226-285`.  Its use for the sorted-pair quotient is discussed explicitly
in `better_bound/paper.tex:2694-2712,3797-3812`.  The paper also records that this ordinary grouped
route does not validate either archived `2.36xx` certificate after correct conditional-entropy
accounting.  Accordingly, this module proves only the exact whole-group tensor restriction; it
makes no entropy, survivor-count, value, or exponent claim.

## Reference

- [CoppersmithWinograd1990] Don Coppersmith and Shmuel Winograd, *Matrix Multiplication via
  Arithmetic Progressions*.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Group every surviving label of the two-address sorted-pair residual into one block.

On the residual support, X and Y already have only the label `01`; hence the only nontrivial
identification made by this map is between the two surviving Z labels `02` and `11`. -/
def cwSortedPair112ResidualGrouping :
    ∀ _c : Leg, SplitWord 1 → Unit :=
  fun _c _label ↦ ()

/-- The unique grouped leg-word address at positive-power depth `n`. -/
def cwSortedPair112ResidualGroupedTarget (n : ℕ) :
    BlockAddress (fun _c : Leg ↦ PositiveWord Unit n) :=
  fun _c ↦ positiveWordConst () n

/-- Mapping any sorted-pair label word through the residual grouping gives the unique Unit word.

Proof sketch: recurse on the positive word.  Both the prefix and the final letter become the
corresponding constant Unit word. -/
theorem positiveWordMap_cwSortedPair112ResidualGrouping
    (c : Leg) (n : ℕ) (word : PositiveWord (SplitWord 1) n) :
    positiveWordMap (cwSortedPair112ResidualGrouping c) n word =
      positiveWordConst () n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rcases word with ⟨headWord, last⟩
      change
        (positiveWordMap (cwSortedPair112ResidualGrouping c) n headWord, ()) =
          (positiveWordConst () n, ())
      rw [ih headWord]

/-- Every one-letter fiber of the constant residual grouping is the complete two-address cut.

Proof sketch: the coarse target is unique, so the fiber predicate is true at every address already
in the residual support.  Filtering therefore leaves the support unchanged, and constituents are
definitionally unchanged. -/
theorem cwSortedPair112ResidualGrouping_fiber_eq
    (K : Type u) [CommRing K] (q : ℕ)
    (target : BlockAddress (fun _c : Leg ↦ Unit)) :
    ((((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).withSupport
        cwSortedPair112ResidualSupport).coarseningFiber
      cwSortedPair112ResidualGrouping target) =
      (((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).withSupport
        cwSortedPair112ResidualSupport) := by
  apply PartitionedTensor.ext
  · change
      cwSortedPair112ResidualSupport.filter (fun source ↦
        coarsenBlockAddress cwSortedPair112ResidualGrouping source = target) =
        cwSortedPair112ResidualSupport
    apply Finset.filter_eq_self.mpr
    intro source _hsource
    exact Subsingleton.elim _ _
  · rfl

/-- At every positive-power depth, the unique grouped fiber is the complete power of the
two-address residual cut.

Proof sketch: every label word maps to the constant Unit word by
`positiveWordMap_cwSortedPair112ResidualGrouping`, so the fiber filter retains the entire positive
power support.  Constituents remain definitionally identical. -/
theorem cwSortedPair112ResidualPositivePower_groupingFiber_eq
    (K : Type u) [CommRing K] (q n : ℕ) :
    (((((cwChunkPartitionedTensor K q 1).coarsen
            cwSortedPairChunkCoarsening).withSupport
          cwSortedPair112ResidualSupport).positivePower n).coarseningFiber
        (fun c ↦ positiveWordMap (cwSortedPair112ResidualGrouping c) n)
        (cwSortedPair112ResidualGroupedTarget n)) =
      ((((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).withSupport
        cwSortedPair112ResidualSupport).positivePower n) := by
  apply PartitionedTensor.ext
  · change
      (((((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).withSupport
        cwSortedPair112ResidualSupport).positivePower n).support.filter
        (fun source ↦
          coarsenBlockAddress
            (fun c ↦ positiveWordMap (cwSortedPair112ResidualGrouping c) n)
            source = cwSortedPair112ResidualGroupedTarget n)) =
      ((((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).withSupport
        cwSortedPair112ResidualSupport).positivePower n).support
    apply Finset.filter_eq_self.mpr
    intro source _hsource
    funext c
    exact positiveWordMap_cwSortedPair112ResidualGrouping c n (source c)
  · rfl

/-- The complete grouped power of the sorted-pair residual restricts factorwise to the word tensor
of established four-block CW `(112)` partitions.

In human-readable terms, neither of the two residual Z addresses is discarded.  At every word
position, the entire two-address group is sent by the committed finite restriction to
`(cw112PartitionedTensor K q).realize`; the generic whole-fiber theorem then tensors all those
restrictions together.  This four-address partition is the input to the later type selection and
X/Y isolation.  Only after fixing one common Z word does that later pipeline construct a genuine
`CTensor.partitioned` object.

Proof sketch: rewrite the residual power as its unique Unit-valued coarsening fiber.  Apply
`Restricts.positivePower_coarseningFiber_restricts_positiveWordTensor`, using
`cwSortedPair112ResidualGrouping_fiber_eq` to reduce every factor premise to the committed
one-letter restriction `cwSortedPair112ResidualCut_restricts_partitioned`. -/
theorem cwSortedPair112ResidualPositivePower_restricts_wordTensor
    (K : Type u) [CommRing K] (q n : ℕ) :
    Restricts
      (((((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).withSupport
        cwSortedPair112ResidualSupport).positivePower n).realize)
      (positiveWordTensor
        (fun _address : BlockAddress (fun _c : Leg ↦ Unit) ↦
          LegModuleFamily.of.{u, u} (K := K)
            (PartitionedSpace K (CW112PartitionBlockSpace K q)))
        (fun _address ↦ (cw112PartitionedTensor K q).realize)
        n ((positiveWordBlockAddressEquiv (fun _c : Leg ↦ Unit) n).symm
          (cwSortedPair112ResidualGroupedTarget n))) := by
  rw [← cwSortedPair112ResidualPositivePower_groupingFiber_eq K q n]
  apply Restricts.positivePower_coarseningFiber_restricts_positiveWordTensor
  intro target
  rw [cwSortedPair112ResidualGrouping_fiber_eq K q target]
  exact cwSortedPair112ResidualCut_restricts_partitioned K q

end AlgebraicComplexity.Examples
