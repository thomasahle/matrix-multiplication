/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveRelaxedCoarseFamily
import AlgebraicComplexity.Tensor.SingleLegHoleRepair

set_option autoImplicit false

/-!
# Presence saturation for the relaxed recursive CW marked family

The relaxed recursive Coppersmith--Winograd hashing family is deliberately larger than the
coarse support of the approximate parent tensor: its ambient family contains every abstract
ordered child-shape word with the prescribed marginals, including addresses with no fine
preimage.  This distinction is essential while counting competitors, but a downstream source
result should not have to provide one fine witness separately for every marked target.

This module proves the missing orbit bridge.  Its reusable first theorem transports *presence*
between two relaxed ambient quotient addresses with the same tagged ordered-left multiplicity.
The proof opens one supported coarse address into a fine witness, moves all parent positions by
the canonical same-type permutation, uses the structure relabeling of the approximate
alpha-marginal tensor to preserve fine support, and coarsens the moved witness again.  Tightness
of the relaxed ambient family identifies its quotient with the desired target.

For the marked family, no region table is needed.  Every marked address has the same visible
joint multiplicity `alpha.coordinateTripleCount`; tagging every position by `PUnit.unit`
therefore puts all marked addresses in one orbit.  Consequently one address belonging to both
the relaxed marked family and the actual approximate coarsened support saturates the entire
relaxed marked family.

The result is local to one `alpha` and one recursive node.  It does not construct the initial
fine witness, compare different split types, perform hashing or compatibility cleanup, or make
an asymptotic counting claim.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*, Section 6.2, Claim
  `claim:constituent-hash-quantities`, and Lemma `lem:more-asym-hash-constituent`;
  `papers/sources/2404.16349/constituent.tex:177-232`.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*, Lemma
  `lem:paired-recursive-normalization`; `better_bound/paper.tex:1009-1034`, and the marked-orbit
  presence propagation described at `better_bound/paper.tex:2783-2788`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- Presence in the approximate coarsened alpha-marginal tensor transports across one relaxed
ambient same-tagged-multiplicity orbit.

`left` is the desired target and `right` is the already present reference.  This order is
important: `cwRecursivePositionPermOfSameTaggedMultiplicity` then relabels `right` to `left`.

Proof sketch: unpack `hright` through `coarsen_support` to obtain a supported fine address.  Apply
the approximate selected term's position structure relabeling to that fine address.  Its
legwise block equivalence is the positive-word position action, so
`cwRecursiveChildGroup_positionRelabel` identifies the new quotient with the paired coarse
position action.  The relaxed-ambient same-type theorem identifies that action with `left`, and
the moved fine witness is repacked through `coarsen_support`. -/
theorem cwRecursiveApproximateCoarsened_mem_of_sameTaggedMultiplicity
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (left right : CWRecursiveCoarseAddress depth n)
    (hleft : left ∈ cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (hright : right ∈
      (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).support)
    (htype : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma left) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma right)) :
    left ∈ (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
      K q term hmultiplicity epsilon sigma alpha).support := by
  classical
  let tau := cwRecursivePositionPermOfSameTaggedMultiplicity
    partAt sigma left right htype
  have hrightAmbient :
      right ∈ cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha :=
    cwRecursiveApproximateCoarsened_support_subset_relaxedAmbient
      K q term hmultiplicity epsilon sigma alpha hright
  have hcoarseRelabel :
      cwRecursivePositionRelabelCoarseAddress depth n tau right = left := by
    dsimp only [tau]
    exact
      cwRecursivePositionRelabelCoarseAddress_of_relaxedAmbient_sameTaggedMultiplicity
        partAt term sigma alpha left right hleft hrightAmbient htype
  have hrightImage := hright
  change right ∈
    ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).coarsen
        (cwRecursiveChildCoarsening depth n)).support at hrightImage
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at hrightImage
  obtain ⟨rightFine, hrightFine, hrightGroup⟩ := hrightImage
  change cwRecursiveChildGroup depth n rightFine = right at hrightGroup
  let relabeling :=
    cwRecursiveApproximateAlphaMarginalSelectedTermPositionRelabeling
      K q term hmultiplicity epsilon sigma alpha tau
  let movedFine := blockAddressCongr relabeling.partEquiv rightFine
  have hmovedFine : movedFine ∈
      (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support := by
    exact PartitionedTensor.StructureRelabeling.mem_support_blockAddressCongr
      relabeling hrightFine
  have hmovedFine_eq : movedFine = fun physicalLeg ↦
      positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau
          (rightFine physicalLeg) := by
    funext physicalLeg
    simp only [movedFine, blockAddressCongr_apply]
    rw [show relabeling.partEquiv physicalLeg =
        positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau by
      exact
        cwRecursiveApproximateAlphaMarginalSelectedTermPositionRelabeling_partEquiv
          K q term hmultiplicity epsilon sigma alpha tau physicalLeg]
  have hmovedGroup : cwRecursiveChildGroup depth n movedFine = left := by
    calc
      cwRecursiveChildGroup depth n movedFine =
        cwRecursivePositionRelabelCoarseAddress depth n tau
          (cwRecursiveChildGroup depth n rightFine) := by
            rw [hmovedFine_eq]
            exact cwRecursiveChildGroup_positionRelabel depth n tau rightFine
      _ = cwRecursivePositionRelabelCoarseAddress depth n tau right := by
        rw [hrightGroup]
      _ = left := hcoarseRelabel
  change left ∈
    ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).coarsen
        (cwRecursiveChildCoarsening depth n)).support
  rw [PartitionedTensor.coarsen_support, Finset.mem_image]
  refine ⟨movedFine, hmovedFine, ?_⟩
  change cwRecursiveChildGroup depth n movedFine = left
  exact hmovedGroup

/-- One present marked reference saturates the full relaxed marked recursive CW family.

The hypothesis supplies one `reference` in both the abstract marked family and the actual
approximate coarsened support.  No cardinality table or generated missing-target certificate is
required.

Proof sketch: marked-family image witnesses identify the visible left-triple multiplicity of
both `target` and `reference` with `alpha.coordinateTripleCount`.  Mapping those triples through
the constant-tag embedding `triple ↦ (PUnit.unit, triple)` gives equal tagged multiplicities.
Both addresses are relaxed ambient, so the generic transport theorem moves the one supported
reference witness to the arbitrary marked target. -/
theorem cwRecursiveRelaxedMarkedCoarseSupport_subset_approximateCoarsened_of_presentReference
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (reference : CWRecursiveCoarseAddress depth n)
    (hreference :
      reference ∈ cwRecursiveRelaxedMarkedCoarseSupport term sigma alpha ∧
      reference ∈ (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).support) :
    cwRecursiveRelaxedMarkedCoarseSupport term sigma alpha ⊆
      (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).support := by
  classical
  intro target htarget
  have markedVisibleMultiplicity : ∀
      {address : CWRecursiveCoarseAddress depth n},
      address ∈ cwRecursiveRelaxedMarkedCoarseSupport term sigma alpha →
        WordType.multiplicity
            (cwRecursiveLogicalLeftTripleWord sigma address) =
          alpha.coordinateTripleCount := by
    intro address haddress
    unfold cwRecursiveRelaxedMarkedCoarseSupport at haddress
    obtain ⟨word, hword, rfl⟩ := Finset.mem_image.mp haddress
    exact (cwRecursiveMatchesAlpha_coarseAddressOfLeftShapeWord_iff
      term sigma alpha word).2 hword
  have htargetVisible := markedVisibleMultiplicity htarget
  have hreferenceVisible := markedVisibleMultiplicity hreference.1
  let partAt : Fin (n + 1) → PUnit.{1} := fun _ ↦ PUnit.unit
  have htag :
      WordType.multiplicity
          (cwRecursiveTaggedLeftTripleWord partAt sigma target) =
        WordType.multiplicity
          (cwRecursiveTaggedLeftTripleWord partAt sigma reference) := by
    change WordType.multiplicity
        ((fun triple ↦ (PUnit.unit, triple)) ∘
          cwRecursiveLogicalLeftTripleWord sigma target) =
      WordType.multiplicity
        ((fun triple ↦ (PUnit.unit, triple)) ∘
          cwRecursiveLogicalLeftTripleWord sigma reference)
    rw [WordType.multiplicity_comp_eq_mappedType,
      WordType.multiplicity_comp_eq_mappedType,
      htargetVisible, hreferenceVisible]
  exact
    cwRecursiveApproximateCoarsened_mem_of_sameTaggedMultiplicity
      K q partAt term hmultiplicity epsilon sigma alpha target reference
        (cwRecursiveRelaxedMarkedCoarseSupport_subset_ambient
          term sigma alpha htarget) hreference.2 htag

end AlgebraicComplexity.Examples
