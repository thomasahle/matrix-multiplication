/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCoarseHashing
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveChildWordCore
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveCompatibility
import AlgebraicComplexity.Tensor.PartitionedCoarseningInterface

set_option autoImplicit false

/-!
# The recursive child quotient of a CW constituent

The recursive constituent theorem uses two related but different words.  For `n+1` parent
occurrences, the ordered split law `alpha` is the type of the `n+1` **left** children.  Hashing
and compatibility, however, see all `2(n+1)` labelled children: left occurrences followed by
their right complements.

This file exposes both words as honest leg-local maps on the selected parent partition, together
with the induced address-level child group.  It then performs the three marginal `alpha`
selections by ordinary variable zero-outs and coarsens the result by the full labelled-child word.
Whole-parent total weights do not occur in this quotient; inside a fixed constituent they would be
constant and hence could not model Proposition 6.3.

No hashing estimate, compatibility count, repair theorem, or target degeneration is assumed.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- Legwise full child-word quotient.  Unlike `cwExactInterfaceCoarsening`, this map is
nonconstant inside a fixed parent constituent. -/
def cwRecursiveChildCoarsening (depth n : ℕ) :
    ∀ _c : Leg,
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n →
        (Fin ((n + 1) + (n + 1)) → CWRecursiveChildDigit depth) :=
  fun _c ↦ cwRecursiveLabelledChildWord depth n

/-- The complete labelled-child weight address attached to one fine parent address.

This is the address-level form of `cwRecursiveChildCoarsening`; it belongs with the quotient map
itself and is independent of the later hashing and compatibility cleanup. -/
def cwRecursiveChildGroup (depth n : ℕ) :
    BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) →
      CWRecursiveCoarseAddress depth n :=
  coarsenBlockAddress (cwRecursiveChildCoarsening depth n)

/-- Reading one leg of the address-level child group is the labelled child word of that leg. -/
@[simp] theorem cwRecursiveChildGroup_apply (depth n : ℕ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (physicalLeg : Leg) :
    cwRecursiveChildGroup depth n address physicalLeg =
      cwRecursiveLabelledChildWord depth n (address physicalLeg) :=
  rfl

/-- Physical-leg predicate imposing the marginal of one oriented ordered split type. -/
def CWRecursiveKeepsAlphaMarginal
    {depth n : ℕ} {term : ExactInterfaceTermParameters (depth + 1)}
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (physicalLeg : Leg)
    (word : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) : Prop :=
  WordType.multiplicity (cwRecursiveLeftChildWord depth n word) =
    alpha.marginalCount (sigma.symm physicalLeg)

noncomputable instance cwRecursiveKeepsAlphaMarginalDecidable
    {depth n : ℕ} {term : ExactInterfaceTermParameters (depth + 1)}
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (physicalLeg : Leg)
    (word : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    Decidable (CWRecursiveKeepsAlphaMarginal sigma alpha physicalLeg word) := by
  classical
  unfold CWRecursiveKeepsAlphaMarginal
  infer_instance

/-- The selected parent interface term after the three exact `alpha` marginal zero-outs. -/
noncomputable def cwRecursiveAlphaMarginalSelectedTerm
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :=
  (cwSelectedExactInterfaceTerm K q term hmultiplicity).select
    (CWRecursiveKeepsAlphaMarginal sigma alpha)

@[simp] theorem mem_cwRecursiveAlphaMarginalSelectedTerm_support
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)) :
    address ∈ (cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).support ↔
      address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support ∧
        ∀ physicalLeg,
          WordType.multiplicity
              (cwRecursiveLeftChildWord depth n (address physicalLeg)) =
            alpha.marginalCount (sigma.symm physicalLeg) := by
  classical
  simp [cwRecursiveAlphaMarginalSelectedTerm, CWRecursiveKeepsAlphaMarginal]

/-- Marginal selection is an actual legwise variable restriction. -/
theorem cwSelectedExactInterfaceTerm_restricts_recursiveAlphaMarginals
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Restricts (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize
      (cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).realize := by
  classical
  exact Tensor.Restricts.partitionedSelect
    (cwSelectedExactInterfaceTerm K q term hmultiplicity)
    (CWRecursiveKeepsAlphaMarginal sigma alpha)

/-- Regroup the marginal-selected parent term by the full labelled child words. -/
noncomputable def cwRecursiveCoarsenedAlphaMarginalTerm
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :=
  (cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha).coarsen
    (cwRecursiveChildCoarsening depth n)

/-- Coarsening the selected term by full child words is an isomorphism, hence an exact
restriction. -/
theorem cwRecursiveAlphaMarginalSelectedTerm_restricts_coarsened
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Restricts
      (cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).realize
      (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).realize :=
  Tensor.Restricts.partitionedCoarsen
    (cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha)
    (cwRecursiveChildCoarsening depth n)

/-- The labelled-child quotient is the coordinate projection of the compatibility model's
coarse word, in physical coordinates. -/
theorem cwRecursiveLabelledChildWord_eq_model_get
    {Part : Type*} (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (physicalLeg : Leg) :
    cwRecursiveLabelledChildWord depth n (address physicalLeg) =
      fun occurrence ↦
        ⟨((cwRecursiveChildCompatibilityModel depth n partAt).coarse
            address occurrence).get physicalLeg, by
          have hweight := recursiveChildCompatibilityModel_hasCoarseWeights
            (fun _c ↦ cwChunkSplitWord (depth + 1)) partAt address physicalLeg occurrence
          have hweight' :
              splitWordWeight (positiveWordLabelledChildren
                (cwChunkSplitWord (depth + 1)) (address physicalLeg) occurrence) =
                ((cwRecursiveChildCompatibilityModel depth n partAt).coarse
                  address occurrence).get physicalLeg := by
            simpa only [cwRecursiveChildCompatibilityModel,
              recursiveChildCompatibilityModel] using hweight
          rw [← hweight']
          exact Nat.lt_succ_iff.mpr (splitWordWeight_le_coarseTotal depth _)⟩ := by
  funext occurrence
  apply Fin.ext
  change (cwRecursiveLabelledChildWord depth n (address physicalLeg) occurrence : ℕ) =
    ((cwRecursiveChildCompatibilityModel depth n partAt).coarse
      address occurrence).get physicalLeg
  have hweight := recursiveChildCompatibilityModel_hasCoarseWeights
    (fun _c ↦ cwChunkSplitWord (depth + 1)) partAt address physicalLeg occurrence
  have hweight' :
      splitWordWeight (positiveWordLabelledChildren
        (cwChunkSplitWord (depth + 1)) (address physicalLeg) occurrence) =
        ((cwRecursiveChildCompatibilityModel depth n partAt).coarse
          address occurrence).get physicalLeg := by
    simpa only [cwRecursiveChildCompatibilityModel,
      recursiveChildCompatibilityModel] using hweight
  rw [← hweight']
  refine Fin.addCases ?_ ?_ occurrence
  · intro sample
    rw [cwRecursiveLabelledChildWord_left,
      positiveWordLabelledChildren_left]
    rfl
  · intro sample
    rw [cwRecursiveLabelledChildWord, Fin.append_right,
      positiveWordLabelledChildren_right]

end AlgebraicComplexity.Examples
