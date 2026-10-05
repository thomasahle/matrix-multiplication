/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarginalSelect

/-!
# The retained direct sum, before any leaf is chosen

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoPlainStage.lean`'s
`dwz63_plainStage_of_uniformLeaf` ends by sending every retained constituent to *one uniform leaf*,
which is right for the no-holes route but bakes that leaf into the statement.  The hole route needs
the same work stopped one step earlier: the plain power restricted onto the direct sum of the
retained constituents **as they are**, with no leaf chosen, so that
`restricts_indexedDirectSum_segmentedHoleRepair_batched` can take over from there.

`dwz63_plainRetainedDirectSum` is exactly that prefix --- the proof of
`dwz63_plainStage_of_uniformLeaf` minus its final `.trans` --- so the two routes share it instead
of rebuilding it.  It is factored into a new module because the stage module is frozen.

The three committed pieces it composes are

* `Tensor.Restricts.power_partitionedPositivePower` (`Tensor/PartitionedPower.lean:645`), opening
  the plain power as the positive power of the fifteen-block partition;
* `dwz63_restricts_positivePower_plainJointRetained`, the marginal cut composed with the hash;
* `Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum`
  (`Tensor/PartitionedDirectSum.lean:125`), splitting the retained subpartition into constituents.

`hlegwise` stays explicit.  On the hole route its `Z` half is discharged downstream rather than
here: Additional Zeroing-Out Step 2 makes each surviving small block useful for exactly one
retained triple (`usefulFor_of_notMem_dwz63HoleSet`), and that fine-level disjointness is what
licenses the direct sum despite the shared coarse `Z`-blocks.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

section RetainedSum

variable {R : Type v} [Field R]

/-- **The plain power restricts onto the direct sum of the retained constituents.**

No leaf is chosen, so both the no-holes route (which then maps every constituent to one uniform
leaf) and the hole route (which then applies the segmented Hole Lemma) consume this same
statement. -/
theorem dwz63_plainRetainedDirectSum [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (hlegwise : IsLegwiseInjective
      (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)) :
    Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      (Tensor.indexedDirectSum
        (fun a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) ↦
          (dwz63PlainMarginalTypicalPower K n t).constituent a.1)) :=
  (Tensor.Restricts.power_partitionedPositivePower (cwSquarePartitionedTensor K dwz63Q) n).trans
    ((dwz63_restricts_positivePower_plainJointRetained K hinj n t markedWords hmarked B hB
        seed).trans
      (Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum
        ((dwz63PlainMarginalTypicalPower K n t).withSupport
          (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)) hlegwise))

end RetainedSum

end AlgebraicComplexity.Examples
