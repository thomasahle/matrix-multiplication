/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainCopyCount
import AlgebraicComplexity.MatrixMultiplication.SymSixUniformLeaf

/-!
# The plain-power stage onto a uniform leaf

Layer 4 (`AlgebraicComplexity/Examples/`).  `restricts_power_symSix_of_plainStage`
(`MatrixMultiplication/SymSixUniformLeaf.lean:92`) consumes a **plain-power** stage onto `ι` copies
of *one* uniform leaf and returns the `sym₆` stage onto `ι ^ 6` copies of `sym₆` of that leaf.  So
what the count lane owes is the plain stage, and the sixth power of the copy count comes out for
free --- on the weight side by `HasTauWeight.symSix_indexedDirectSum_uniform`, on the count side by
`pow_six_of_copyCount`.

That the leaf is uniform is what the paper supplies: all retained broken copies degenerate to the
same standard-form tensor `𝒯*` (`global_value.tex:110-113`), which is exactly why every one of the
`ι ^ 6` terms --- not merely the diagonal ones --- is `sym₆(𝒯*)`.

## The chain

`Tensor.Restricts.power_partitionedPositivePower` (`Tensor/PartitionedPower.lean:645`) opens the
plain power as the positive power of the fifteen-block partition;
`dwz63_restricts_positivePower_plainJointRetained` cuts to the marginal-typical ambient and hashes;
`partitionedLegwiseInjective_to_indexedDirectSum` splits the retained subpartition into its
constituents; and `Tensor.Restricts.indexedDirectSum` sends each constituent to the common leaf.

## The two hypotheses, and why they are hypotheses

`hlegwise` asks for legwise injectivity of the retained family.  The hash supplies the `X` and `Y`
halves (`dwz63_x_injOn_plainJointRetained` and the engine's `Y` certificate); the `Z` half is the
subject of the open §0 adjudication, since `[DuanWuZhou2022]`'s retained triples deliberately
*share* large `Z`-blocks (`global_value.tex:28`, and branch two of the count is `N_Z / p_comp >
N_Z`).  `hleaf` is the hole-repair obligation, which lands on the same adjudication.  Both are
therefore left explicit: the stage below is complete and un-gated, and when §0 settles only these
two premises get discharged --- no statement here changes.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w

section Stage

variable {R : Type v} [Field R]

/-- **The plain-power stage onto a uniform leaf.**

This is the object `restricts_power_symSix_of_plainStage` consumes.  The index is the retained
family of the plain hash at the marginal-typical ambient. -/
theorem dwz63_plainStage_of_uniformLeaf [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (hlegwise : IsLegwiseInjective
      (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed))
    {W : Leg → Type max u v} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    (leaf : Tensor3 K W)
    (hleaf : ∀ a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed),
      Restricts ((dwz63PlainMarginalTypicalPower K n t).constituent a.1) leaf) :
    Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      (Tensor.indexedDirectSum
        (V := fun _ : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) ↦ W)
        fun _ ↦ leaf) := by
  classical
  have hsplit :
      Restricts ((dwz63PlainMarginalTypicalPower K n t).withSupport
          (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)).realize
        (Tensor.indexedDirectSum
          (fun a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) ↦
            (dwz63PlainMarginalTypicalPower K n t).constituent a.1)) :=
    Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum
      ((dwz63PlainMarginalTypicalPower K n t).withSupport
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)) hlegwise
  exact ((Tensor.Restricts.power_partitionedPositivePower
      (cwSquarePartitionedTensor K dwz63Q) n).trans
    ((dwz63_restricts_positivePower_plainJointRetained K hinj n t markedWords hmarked B hB
      seed).trans hsplit)).trans (Tensor.Restricts.indexedDirectSum hleaf)

/-- **The `sym₆` stage, with the sixth power of the copy count for free.**

`restricts_power_symSix_of_plainStage` applied to the stage above: `m` retained copies of one
uniform leaf become `m ^ 6` copies of `sym₆` of that leaf, which is precisely the ratio between a
copy budget stated per position and the master theorem's `6 N`. -/
theorem dwz63_restricts_power_symSix_of_plainStage [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (hlegwise : IsLegwiseInjective
      (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed))
    {W : Leg → Type max u v} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    (leaf : Tensor3 K W)
    (hleaf : ∀ a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed),
      Restricts ((dwz63PlainMarginalTypicalPower K n t).constituent a.1) leaf) :
    Restricts
      (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (n + 1))
      (Tensor.indexedDirectSum
        (fun _ : (((dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) ×
              (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)) ×
            (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)) ×
          (((dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) ×
              (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)) ×
            (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)) ↦
          symSix K leaf)) :=
  restricts_power_symSix_of_plainStage n
    (dwz63_plainStage_of_uniformLeaf K hinj n t markedWords hmarked B hB seed hlegwise leaf hleaf)

end Stage

end AlgebraicComplexity.Examples
