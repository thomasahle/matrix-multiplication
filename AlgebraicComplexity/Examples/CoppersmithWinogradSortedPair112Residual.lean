/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112Partition
import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordQuotient
import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingValue
import AlgebraicComplexity.Tensor.CoarsenedSupportPreimage

set_option autoImplicit false

/-!
# The sorted-pair residual over the exceptional CW `(112)` constituent

Layer 4 (`AlgebraicComplexity/Examples/`).  In the tensor square, the exceptional constituent
`T^2_{112}` is the sum of the four products

`T_002 tensor T_110`, `T_110 tensor T_002`, `T_011 tensor T_101`, and
`T_101 tensor T_011`.

This is the decomposition displayed in `[almanwilliams2024refined]`,
`papers/sources/2010.05846/final-TheoretiCS.tex:613-629`, and in the original
Coppersmith--Winograd analysis `[coppersmith1990matrix]`, journal pp. 270--272.  Under the
globally fixed sorted-pair quotient, the first two raw addresses have coarse label
`(01,01,02)`, while the last two have coarse label `(01,01,11)`.  Thus the residual is a cut to
**two** coarse addresses, not one coarse constituent.

This file proves the exact finite bridge.  It defines the two-address coarse support, computes
its complete fine preimage as the four-address `cwSquareSourceFiber cwSquare112`, identifies the
coarse cut with that fine cut by the generic coarsening-preimage isomorphism, and restricts the
cut onto the established four-block C-tensor `cw112PartitionedTensor`.

The sorted-pair proposal is discussed in `better_bound/paper.tex:2664-2673`; the entropy
separation needed by a future word-level use is `better_bound/paper.tex:1622-1648`.  No entropy,
word grouping, hashing rate, repair theorem, value bound, or matrix-multiplication exponent is
claimed here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- **The exceptional sorted-pair residual occupies exactly two quotient addresses.**

The corner products `002 tensor 110` and `110 tensor 002` land at `(01,01,02)`; the cross
products `011 tensor 101` and `101 tensor 011` land at `(01,01,11)`. -/
def cwSortedPair112ResidualSupport :
    Finset (BlockAddress (fun _c : Leg ↦ SplitWord 1)) :=
  {ofLegs (V := fun _c : Leg ↦ SplitWord 1)
      (cwSplitPair 0 1) (cwSplitPair 0 1) (cwSplitPair 0 2),
    ofLegs (V := fun _c : Leg ↦ SplitWord 1)
      (cwSplitPair 0 1) (cwSplitPair 0 1) (cwSplitPair 1 1)}

/-- **The complete fine preimage of the two sorted-pair addresses is precisely the four raw
summands of `T^2_{112}`.**

Proof sketch: unfold the depth-one chunk into the square of the six-address CW partition.  Its
support has only thirty-six ordered address pairs.  Sorting the two digits on every leg sends
exactly the two corner orders to `(01,01,02)` and the two cross orders to `(01,01,11)`; the small
closed computation is checked by the kernel. -/
theorem cwSortedPair112ResidualSupport_preimage
    (K : Type u) [CommRing K] (q : ℕ) :
    coarseningPreimageSupport (cwChunkPartitionedTensor K q 1)
        cwSortedPairChunkCoarsening cwSortedPair112ResidualSupport =
      cwSquareSourceFiber cwSquare112 := by
  classical
  change cwSquareRawSupport.filter (fun source ↦
      coarsenBlockAddress cwSortedPairChunkCoarsening source ∈
        cwSortedPair112ResidualSupport) =
    cwSquareSourceFiber cwSquare112
  rw [cwSquareSourceFiber_112]
  decide

/-- **Cutting the sorted-pair quotient to its two exceptional addresses is isomorphic to
retaining the four raw `T^2_{112}` summands before quotienting.**

Proof sketch: the two quotient addresses lie in the coarsened support, as witnessed by their four
raw preimages.  Apply `Isomorphic.coarsen_withSupport_preimage`, then replace its abstract
preimage support by the exact finite computation above.  This is only regrouping of block spaces;
no tensor term is discarded. -/
theorem cwSortedPair112ResidualCut_isomorphic_fineFiber
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic
      ((((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).withSupport
        cwSortedPair112ResidualSupport).realize)
      ((cwChunkPartitionedTensor K q 1).withSupport
        (cwSquareSourceFiber cwSquare112)).realize := by
  classical
  have hsupport : cwSortedPair112ResidualSupport ⊆
      ((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).support := by
    change cwSortedPair112ResidualSupport ⊆
      cwSquareRawSupport.image
        (coarsenBlockAddress cwSortedPairChunkCoarsening)
    decide
  have hisomorphic := Isomorphic.coarsen_withSupport_preimage
    (cwChunkPartitionedTensor K q 1) cwSortedPairChunkCoarsening
    cwSortedPair112ResidualSupport hsupport
  rwa [cwSortedPair112ResidualSupport_preimage K q] at hisomorphic

/-- **The two-address sorted-pair residual restricts onto the established exceptional `(112)`
C-tensor partition.**

`Restricts A B` means that legwise linear maps send the source `A` to the target `B`; here the
source is the whole two-address quotient cut and the target is
`(cw112PartitionedTensor K q).realize`.

Proof sketch: first undo the sorted-pair regrouping using
`cwSortedPair112ResidualCut_isomorphic_fineFiber`.  Regroup the same four raw terms by ordinary
degree sum; their complete preimage is the singleton square constituent `112`.  Project that
singleton cut to its constituent, then compose with the already-proved restriction from the
square `112` constituent to its four-block C-tensor presentation. -/
theorem cwSortedPair112ResidualCut_restricts_partitioned
    (K : Type u) [CommRing K] (q : ℕ) :
    Restricts
      ((((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).withSupport
        cwSortedPair112ResidualSupport).realize)
      (cw112PartitionedTensor K q).realize := by
  classical
  refine (cwSortedPair112ResidualCut_isomorphic_fineFiber K q).restricts.trans ?_
  have hsupport : ({cwSquare112} : Finset CWSquareAddress) ⊆
      ((cwChunkPartitionedTensor K q 1).coarsen cwSquareDegreeMap).support := by
    change ({cwSquare112} : Finset CWSquareAddress) ⊆ cwSquareSupport
    rw [cwSquareSupport_eq_antidiagonal]
    decide
  have hpreimage :
      coarseningPreimageSupport (cwChunkPartitionedTensor K q 1)
          cwSquareDegreeMap ({cwSquare112} : Finset CWSquareAddress) =
        cwSquareSourceFiber cwSquare112 := by
    change cwSquareRawSupport.filter (fun source ↦
        coarsenBlockAddress cwSquareDegreeMap source ∈
          ({cwSquare112} : Finset CWSquareAddress)) =
      cwSquareRawSupport.filter (fun source ↦
        coarsenBlockAddress cwSquareDegreeMap source = cwSquare112)
    apply Finset.filter_congr
    intro source _hsource
    simp
  have hdegree := Isomorphic.coarsen_withSupport_preimage
    (cwChunkPartitionedTensor K q 1) cwSquareDegreeMap
    ({cwSquare112} : Finset CWSquareAddress) hsupport
  have hfineToDegree :
      Restricts
        ((cwChunkPartitionedTensor K q 1).withSupport
          (cwSquareSourceFiber cwSquare112)).realize
        ((((cwChunkPartitionedTensor K q 1).coarsen
            cwSquareDegreeMap).withSupport
          ({cwSquare112} : Finset CWSquareAddress)).realize) := by
    rw [← hpreimage]
    exact hdegree.symm.restricts
  refine hfineToDegree.trans ?_
  refine (Tensor.Restricts.partitionedConstituent
    (((cwChunkPartitionedTensor K q 1).coarsen cwSquareDegreeMap).withSupport
      ({cwSquare112} : Finset CWSquareAddress)) cwSquare112 (by simp)).trans ?_
  rw [PartitionedTensor.withSupport_constituent]
  change Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare112)
    (cw112PartitionedTensor K q).realize
  exact cwSquareConstituent_112_restricts_partitioned K q

end AlgebraicComplexity.Examples
