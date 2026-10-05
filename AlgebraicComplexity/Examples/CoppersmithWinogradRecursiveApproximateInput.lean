/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradApproximateInterface
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveCoarsening
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibility

/-!
# Approximate parent input for a recursive CW constituent

The standard recursive constituent theorem starts from an approximately prescribed parent
complete-split law, then imposes the exact three marginals of the ordered left-child split type.
The older exact-input client modeled the same hashing and compatibility operations on one exact
parent type.  That tensor is useful for finite semantic tests, but it is too small for the
published sparse-hole argument: almost all independently assembled child-product labels have a
nearby parent type rather than one particular exact type.

This module constructs the correct source-side object.  Its input is still an exact rational
profile record, used only to name the normalized semantic law.  The actual tensor keeps the full
`epsilon` neighborhood, enforces the ordered-split marginals by explicit legwise zero-outs, and
then forms the labelled-child quotient.  Every restriction is built internally from a flat power
of `CW_q`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- Positivity of the sample count carried by a term realized as a positive power. -/
theorem exactInterfaceTerm_multiplicity_pos_of_eq_succ
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    0 < term.multiplicity := by
  rw [hmultiplicity]
  exact Nat.zero_lt_succ n

/-- The normalized semantic parent law associated with an exact rational profile record. -/
noncomputable def cwRecursiveSemanticParentTerm
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    InterfaceTermParameters depth :=
  term.toSemantic (exactInterfaceTerm_multiplicity_pos_of_eq_succ term hmultiplicity)

@[simp] theorem cwRecursiveSemanticParentTerm_multiplicity
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    (cwRecursiveSemanticParentTerm term hmultiplicity).multiplicity = n + 1 := by
  simp [cwRecursiveSemanticParentTerm, hmultiplicity]

@[simp] theorem cwRecursiveSemanticParentTerm_index
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    (cwRecursiveSemanticParentTerm term hmultiplicity).index = term.index := by
  rfl

/-- The approximate parent interface after the three exact ordered-left marginal selections. -/
noncomputable def cwRecursiveApproximateAlphaMarginalSelectedTerm
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :=
  (cwSelectedApproximateInterfaceTerm K q
      (cwRecursiveSemanticParentTerm term hmultiplicity)
      (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity) epsilon).select
    (CWRecursiveKeepsAlphaMarginal sigma alpha)

/-- Reading the ordered left child commutes with a parent-position permutation. -/
theorem cwRecursiveLeftChildWord_positionRelabel_eq_comp
    (depth n : ℕ) (tau : Equiv.Perm (Fin (n + 1)))
    (word : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    cwRecursiveLeftChildWord depth n
        (positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau word) =
      cwRecursiveLeftChildWord depth n word ∘ tau := by
  funext sample
  simp [cwRecursiveLeftChildWord, Function.comp_apply]

/-- The exact ordered-left marginal predicate is invariant under parent-position
permutations. -/
theorem cwRecursiveKeepsAlphaMarginal_positionEquiv_iff
    {depth n : ℕ} {term : ExactInterfaceTermParameters (depth + 1)}
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (physicalLeg : Leg)
    (word : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (tau : Equiv.Perm (Fin (n + 1))) :
    CWRecursiveKeepsAlphaMarginal sigma alpha physicalLeg
        (positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau word) ↔
      CWRecursiveKeepsAlphaMarginal sigma alpha physicalLeg word := by
  unfold CWRecursiveKeepsAlphaMarginal
  rw [cwRecursiveLeftChildWord_positionRelabel_eq_comp]
  have hmultiplicity := WordType.multiplicity_reindex
    (α := CWRecursiveChildDigit depth) tau.symm
      (cwRecursiveLeftChildWord depth n word)
  rw [Equiv.symm_symm] at hmultiplicity
  rw [hmultiplicity]

/-- The approximate parent term with exact ordered-left marginals retains the full symmetric
group action on parent positions. -/
noncomputable def
    cwRecursiveApproximateAlphaMarginalSelectedTermPositionRelabeling
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (tau : Equiv.Perm (Fin (n + 1))) :
    (cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).StructureRelabeling := by
  classical
  unfold cwRecursiveApproximateAlphaMarginalSelectedTerm
  let r := cwSelectedApproximateInterfaceTermPositionRelabeling
    K q (cwRecursiveSemanticParentTerm term hmultiplicity)
      (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity) epsilon tau
  refine r.select (CWRecursiveKeepsAlphaMarginal sigma alpha) ?_
  intro physicalLeg word
  rw [show r.partEquiv physicalLeg =
      positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau by
    dsimp [r]
    exact cwSelectedApproximateInterfaceTermPositionRelabeling_partEquiv
      K q (cwRecursiveSemanticParentTerm term hmultiplicity)
        (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
        epsilon tau physicalLeg]
  have hsymm :
      (positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau).symm =
        positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau.symm := by
    apply Equiv.ext
    intro candidate
    refine (Equiv.symm_apply_eq _).mpr ?_
    have hone : (tau.symm * tau : Equiv.Perm (Fin (n + 1))) = 1 := by
      apply Equiv.ext
      intro i
      simp
    have hmul := positiveWordPositionEquiv_mul
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau.symm tau
    rw [hone, positiveWordPositionEquiv_one] at hmul
    simpa using congrArg (fun e ↦ e candidate) hmul
  rw [hsymm]
  exact cwRecursiveKeepsAlphaMarginal_positionEquiv_iff
    sigma alpha physicalLeg word tau.symm

/-- The concrete relabeling of the approximate alpha-selected term acts by the advertised
position permutation on each physical leg. -/
@[simp] theorem
    cwRecursiveApproximateAlphaMarginalSelectedTermPositionRelabeling_partEquiv
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (tau : Equiv.Perm (Fin (n + 1))) (physicalLeg : Leg) :
    (cwRecursiveApproximateAlphaMarginalSelectedTermPositionRelabeling
      K q term hmultiplicity epsilon sigma alpha tau).partEquiv physicalLeg =
      positiveWordPositionEquiv
        (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau := by
  unfold cwRecursiveApproximateAlphaMarginalSelectedTermPositionRelabeling
  exact cwSelectedApproximateInterfaceTermPositionRelabeling_partEquiv
    K q (cwRecursiveSemanticParentTerm term hmultiplicity)
      (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
      epsilon tau physicalLeg

@[simp] theorem mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)) :
    address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support ↔
      address ∈ (cwSelectedApproximateInterfaceTerm K q
          (cwRecursiveSemanticParentTerm term hmultiplicity)
          (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
          epsilon).support ∧
        ∀ physicalLeg,
          WordType.multiplicity
              (cwRecursiveLeftChildWord depth n (address physicalLeg)) =
            alpha.marginalCount (sigma.symm physicalLeg) := by
  classical
  simp [cwRecursiveApproximateAlphaMarginalSelectedTerm,
    CWRecursiveKeepsAlphaMarginal]

/-- Ordered-split marginal selection is an actual variable restriction of the approximate
parent interface. -/
theorem cwSelectedApproximateInterfaceTerm_restricts_recursiveAlphaMarginals
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Restricts
      (cwSelectedApproximateInterfaceTerm K q
        (cwRecursiveSemanticParentTerm term hmultiplicity)
        (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
        epsilon).realize
      (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).realize := by
  classical
  exact Tensor.Restricts.partitionedSelect
    (cwSelectedApproximateInterfaceTerm K q
      (cwRecursiveSemanticParentTerm term hmultiplicity)
      (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity) epsilon)
    (CWRecursiveKeepsAlphaMarginal sigma alpha)

/-- Complete source-side restriction: a flat power of `CW_q` restricts to the approximate
parent term with the exact ordered-left marginals imposed. -/
theorem cwFlatPower_restricts_recursiveApproximateAlphaMarginals
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Restricts
      (Tensor.power (cwPartitionedTensor K q).realize
        (2 ^ (depth + 1) * (n + 1)))
      (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).realize :=
  (cwFlatPower_selectedApproximateInterfaceTerm_restricts K q
    (cwRecursiveSemanticParentTerm term hmultiplicity)
    (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity) epsilon).trans
      (cwSelectedApproximateInterfaceTerm_restricts_recursiveAlphaMarginals
        K q term hmultiplicity epsilon sigma alpha)

/-- Regroup the approximate marginal-selected parent by its full labelled-child words. -/
noncomputable def cwRecursiveApproximateCoarsenedAlphaMarginalTerm
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :=
  (cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).coarsen
    (cwRecursiveChildCoarsening depth n)

/-- Coarsening the approximate selected term is a structure isomorphism and hence a
restriction. -/
theorem cwRecursiveApproximateAlphaMarginalSelectedTerm_restricts_coarsened
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Restricts
      (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).realize
      (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).realize :=
  Tensor.Restricts.partitionedCoarsen
    (cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha)
    (cwRecursiveChildCoarsening depth n)

/-- Every chunk of an approximately selected parent label has the fixed constituent coordinate.
This uses the explicit support half of approximate consistency, not its numerical tolerance. -/
theorem cwRecursive_parentWeight_of_mem_approximateSelected_support
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedApproximateInterfaceTerm K q
        (cwRecursiveSemanticParentTerm term hmultiplicity)
        (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
        epsilon).support)
    (physicalLeg : Leg) (sample : Fin (n + 1)) :
    splitWordWeight
        (cwChunkSplitWord (depth + 1)
          (positiveWordEquiv _ n (address physicalLeg) sample)) =
      term.index.count physicalLeg := by
  have hdata := ((cwChunkPartitionedTensor K q
    (depth + 1)).mem_selectEncodedApproximateInterfaceTerm_support
      (fun _c ↦ cwChunkSplitWord (depth + 1))
      (cwRecursiveSemanticParentTerm term hmultiplicity)
      (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
      epsilon address).1 haddress
  exact (hdata.2 physicalLeg).1 sample

/-- Approximate input selection preserves the native fine legality because it is a subset of
the positive-power support. -/
theorem cwRecursiveChildCompatibilityModel_isFineLegal_of_mem_approximateSelected_support
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedApproximateInterfaceTerm K q
        (cwRecursiveSemanticParentTerm term hmultiplicity)
        (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
        epsilon).support) :
    (cwRecursiveChildCompatibilityModel depth n partAt).IsFineLegal address := by
  have hdata := ((cwChunkPartitionedTensor K q
    (depth + 1)).mem_selectEncodedApproximateInterfaceTerm_support
      (fun _c ↦ cwChunkSplitWord (depth + 1))
      (cwRecursiveSemanticParentTerm term hmultiplicity)
      (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
      epsilon address).1 haddress
  let dummyPart : Fin (n + 1) → (PUnit : Type) := fun _ ↦ PUnit.unit
  have hparentEncoded :=
    encodedPositiveWordCompatibilityModel_isFineLegal_of_mem_positivePower_support
      (cwChunkPartitionedTensor K q (depth + 1))
      (fun _c ↦ cwChunkSplitWord (depth + 1)) dummyPart
      (cwChunkPartitionedTensor_isEncodedFineLegalOnSupport K q (depth + 1))
      address hdata.1
  have hparent : IsParentFineLegal
      (fun _c ↦ cwChunkSplitWord (depth + 1)) address := by
    simpa [IsParentFineLegal, CompatibilityModel.IsFineLegal, dummyPart,
      encodedPositiveWordCompatibilityModel] using hparentEncoded
  exact recursiveChildCompatibilityModel_isFineLegal
    (fun _c ↦ cwChunkSplitWord (depth + 1)) partAt address hparent

/-- Approximate-input fine legality is preserved after presenting the physical legs in any
logical region orientation.  This uses only the symmetric CW support equation, not symmetry of
the prescribed parent profile. -/
theorem
    cwRecursiveChildCompatibilityModel_isFineLegal_logicalAddress_of_mem_approximateSelected_support
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedApproximateInterfaceTerm K q
        (cwRecursiveSemanticParentTerm term hmultiplicity)
        (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
        epsilon).support) :
    (cwRecursiveChildCompatibilityModel depth n partAt).IsFineLegal
      (logicalAddress sigma address) := by
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  have hphysical : model.IsFineLegal address :=
    cwRecursiveChildCompatibilityModel_isFineLegal_of_mem_approximateSelected_support
      K q partAt term hmultiplicity epsilon address haddress
  intro occurrence position
  have hsum :
      (∑ c : Leg,
        ((model.chunks c (address c) occurrence position : SplitDigit) : ℕ)) = 2 := by
    simpa [Tensor.sum_leg] using hphysical occurrence position
  have hperm :
      (∑ c : Leg,
        ((model.chunks c (address (sigma c)) occurrence position : SplitDigit) : ℕ)) =
      ∑ c : Leg,
        ((model.chunks c (address c) occurrence position : SplitDigit) : ℕ) := by
    change
      (∑ c : Leg,
        ((positiveWordLabelledChildren (cwChunkSplitWord (depth + 1))
          (address (sigma c)) occurrence position : SplitDigit) : ℕ)) =
      ∑ c : Leg,
        ((positiveWordLabelledChildren (cwChunkSplitWord (depth + 1))
          (address c) occurrence position : SplitDigit) : ℕ)
    exact Equiv.sum_comp sigma fun c : Leg ↦
      ((positiveWordLabelledChildren (cwChunkSplitWord (depth + 1))
        (address c) occurrence position : SplitDigit) : ℕ)
  have hlogicalSum :
      (∑ c : Leg,
        ((model.chunks c ((logicalAddress sigma address) c) occurrence position :
          SplitDigit) : ℕ)) = 2 := by
    simpa only [logicalAddress_apply] using hperm.trans hsum
  change
    ((model.chunks .X ((logicalAddress sigma address) .X) occurrence position :
          SplitDigit) : ℕ) +
        ((model.chunks .Y ((logicalAddress sigma address) .Y) occurrence position :
          SplitDigit) : ℕ) +
      ((model.chunks .Z ((logicalAddress sigma address) .Z) occurrence position :
        SplitDigit) : ℕ) = 2
  simpa only [Tensor.sum_leg] using hlogicalSum

/-- On every supported approximate recursive quotient address, the two labelled child digits add
to the fixed parent coordinate.  This conclusion uses only the structural support half of the
approximate selector. -/
theorem cwRecursiveApproximateCoarsenedAlphaMarginalTerm_left_add_right
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n)
    (haddress : address ∈
      (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).support)
    (physicalLeg : Leg) (sample : Fin (n + 1)) :
    (address physicalLeg (Fin.castAdd (n + 1) sample) : ℕ) +
        (address physicalLeg (Fin.natAdd (n + 1) sample) : ℕ) =
      term.index.count physicalLeg := by
  classical
  change address ∈
    ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).coarsen
        (cwRecursiveChildCoarsening depth n)).support at haddress
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hcoarse⟩ := haddress
  have hparent : fine ∈
      (cwSelectedApproximateInterfaceTerm K q
        (cwRecursiveSemanticParentTerm term hmultiplicity)
        (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
        epsilon).support :=
    (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
      K q term hmultiplicity epsilon sigma alpha fine).mp hfine |>.1
  let partAt : Fin (n + 1) → (PUnit : Type) := fun _ ↦ PUnit.unit
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  have hadd := recursiveChildCompatibilityModel_coarse_add_eq_parent
    (fun _c ↦ cwChunkSplitWord (depth + 1)) partAt fine term.index.count
    (cwRecursive_parentWeight_of_mem_approximateSelected_support
      K q term hmultiplicity epsilon fine hparent) physicalLeg sample
  have hleft :
      (address physicalLeg (Fin.castAdd (n + 1) sample) : ℕ) =
        (model.coarse fine (Fin.castAdd (n + 1) sample)).get physicalLeg := by
    rw [← hcoarse]
    exact congrArg Fin.val <| congrFun
      (cwRecursiveLabelledChildWord_eq_model_get depth n partAt fine physicalLeg)
      (Fin.castAdd (n + 1) sample)
  have hright :
      (address physicalLeg (Fin.natAdd (n + 1) sample) : ℕ) =
        (model.coarse fine (Fin.natAdd (n + 1) sample)).get physicalLeg := by
    rw [← hcoarse]
    exact congrArg Fin.val <| congrFun
      (cwRecursiveLabelledChildWord_eq_model_get depth n partAt fine physicalLeg)
      (Fin.natAdd (n + 1) sample)
  rw [hleft, hright]
  simpa only [model, cwRecursiveChildCompatibilityModel] using hadd

/-- Every supported approximate recursive quotient address satisfies the coordinatewise tight
child-total equation. -/
theorem cwRecursiveApproximateCoarsenedAlphaMarginalTerm_coarse_sum
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n)
    (haddress : address ∈
      (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).support)
    (occurrence : Fin ((n + 1) + (n + 1))) :
    (address .X occurrence : ℕ) + (address .Y occurrence : ℕ) +
        (address .Z occurrence : ℕ) = coarseTotal depth := by
  classical
  change address ∈
    ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).coarsen
        (cwRecursiveChildCoarsening depth n)).support at haddress
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hcoarse⟩ := haddress
  have hparent : fine ∈
      (cwSelectedApproximateInterfaceTerm K q
        (cwRecursiveSemanticParentTerm term hmultiplicity)
        (cwRecursiveSemanticParentTerm_multiplicity term hmultiplicity)
        epsilon).support :=
    (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
      K q term hmultiplicity epsilon sigma alpha fine).mp hfine |>.1
  let partAt : Fin (n + 1) → (PUnit : Type) := fun _ ↦ PUnit.unit
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  have hlegal : model.IsFineLegal fine :=
    cwRecursiveChildCompatibilityModel_isFineLegal_of_mem_approximateSelected_support
      K q partAt term hmultiplicity epsilon fine hparent
  have hweights : model.HasCoarseWeights fine :=
    recursiveChildCompatibilityModel_hasCoarseWeights
      (fun _c ↦ cwChunkSplitWord (depth + 1)) partAt fine
  have hsum := model.coarse_sum_eq_coarseTotal fine hlegal hweights occurrence
  have hgroup (c : Leg) :
      address c occurrence =
        cwRecursiveLabelledChildWord depth n (fine c) occurrence := by
    rw [← hcoarse]
    rfl
  have hmodel (c : Leg) :
      (address c occurrence : ℕ) = (model.coarse fine occurrence).get c := by
    rw [hgroup c]
    exact congrArg Fin.val <|
      congrFun (cwRecursiveLabelledChildWord_eq_model_get
        depth n partAt fine c) occurrence
  rw [hmodel .X, hmodel .Y, hmodel .Z]
  change (model.coarse fine occurrence).x + (model.coarse fine occurrence).y +
    (model.coarse fine occurrence).z = coarseTotal depth
  exact hsum

/-- The former exact-input alpha-selected support embeds in the approximate-input version.  This
is a sanity bridge only; the sparse-hole proof uses the much larger approximate support. -/
theorem cwRecursiveAlphaMarginalSelectedTerm_support_subset_approximate
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    (cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha).support ⊆
      (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support := by
  classical
  intro address haddress
  have hdata := (mem_cwRecursiveAlphaMarginalSelectedTerm_support
    K q term hmultiplicity sigma alpha address).1 haddress
  apply (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
    K q term hmultiplicity epsilon sigma alpha address).2
  refine ⟨?_, hdata.2⟩
  exact cwSelectedExactInterfaceTerm_support_subset_approximate
    K q term hmultiplicity hepsilon hdata.1

end AlgebraicComplexity.Examples
