/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveHashing
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateInput
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveFiberNormalization
import AlgebraicComplexity.Combinatorics.RecursiveSplitMarginalCounting

/-!
# The relaxed recursive CW coarse hashing family

The recursive constituent theorem hashes a combinatorial family larger than the coarse image of
one selected fine parent tensor.  Its ambient family consists of every ordered child-shape word
with the three prescribed coordinate marginals; its marked subfamily has the prescribed joint
type.  The complete-split input condition is imposed only on the fine preimage and is deliberately
dropped from the competitor family.

This module constructs that relaxed family as literal labelled-child CW addresses.  A left child
shape determines the right child by complementation, including the self-complementary case.  The
construction is injective, obeys the tight affine equation at every labelled occurrence, and
identifies the marked and ambient cardinalities exactly with `N_alpha` and `N_triple`.

No fine tensor, approximate selector, compatibility zeroing, repair theorem, or asymptotic
estimate occurs in these definitions.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- Turn one abstract ordered-left child-shape word into the full labelled left-plus-right
recursive quotient address.  Physical legs are obtained from logical legs through `sigma`; the
right occurrence is the coordinatewise complement inside the fixed parent constituent. -/
def cwRecursiveCoarseAddressOfLeftShapeWord
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (word : Fin (n + 1) → RecursiveChildShape
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth)) :
    CWRecursiveCoarseAddress depth n :=
  fun physicalLeg occurrence ↦
    let logicalLeg := sigma.symm physicalLeg
    Fin.addCases
      (fun sample ↦ ExactRecursiveSplitType.coordinate logicalLeg (word sample))
      (fun sample ↦ ExactRecursiveSplitType.coordinate logicalLeg
        ((RecursiveChildShape.complementPerm
          (cwRecursiveLogicalParent_total term sigma)) (word sample)))
      occurrence

@[simp] theorem cwRecursiveCoarseAddressOfLeftShapeWord_left
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (word : Fin (n + 1) → RecursiveChildShape
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth))
    (logicalLeg : Leg) (sample : Fin (n + 1)) :
    cwRecursiveCoarseAddressOfLeftShapeWord term sigma word
        (sigma logicalLeg) (Fin.castAdd (n + 1) sample) =
      ExactRecursiveSplitType.coordinate logicalLeg (word sample) := by
  simp [cwRecursiveCoarseAddressOfLeftShapeWord]

@[simp] theorem cwRecursiveCoarseAddressOfLeftShapeWord_right
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (word : Fin (n + 1) → RecursiveChildShape
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth))
    (logicalLeg : Leg) (sample : Fin (n + 1)) :
    cwRecursiveCoarseAddressOfLeftShapeWord term sigma word
        (sigma logicalLeg) (Fin.natAdd (n + 1) sample) =
      ExactRecursiveSplitType.coordinate logicalLeg
        ((RecursiveChildShape.complementPerm
          (cwRecursiveLogicalParent_total term sigma)) (word sample)) := by
  rw [cwRecursiveCoarseAddressOfLeftShapeWord, Fin.addCases_right]
  simp only [Equiv.symm_apply_apply]

/-- The full labelled quotient address remembers its ordered-left child-shape word. -/
theorem cwRecursiveCoarseAddressOfLeftShapeWord_injective
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation) :
    Function.Injective
      (cwRecursiveCoarseAddressOfLeftShapeWord
        (n := n) term sigma) := by
  intro left right heq
  funext sample
  apply RecursiveChildShape.ext
  intro logicalLeg
  have hcoordinate := congrFun
    (congrFun heq (sigma logicalLeg)) (Fin.castAdd (n + 1) sample)
  simpa only [cwRecursiveCoarseAddressOfLeftShapeWord_left,
    ExactRecursiveSplitType.coordinate_val] using congrArg Fin.val hcoordinate

/-- The visible logical left triple is exactly the coordinate observation of the abstract split
word. -/
theorem cwRecursiveLogicalLeftTripleWord_coarseAddressOfLeftShapeWord
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (word : Fin (n + 1) → RecursiveChildShape
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth)) :
    cwRecursiveLogicalLeftTripleWord sigma
        (cwRecursiveCoarseAddressOfLeftShapeWord term sigma word) =
      ExactRecursiveSplitType.coordinateTriple ∘ word := by
  funext sample
  apply Prod.ext
  · exact cwRecursiveCoarseAddressOfLeftShapeWord_left term sigma word .X sample
  · apply Prod.ext
    · exact cwRecursiveCoarseAddressOfLeftShapeWord_left term sigma word .Y sample
    · exact cwRecursiveCoarseAddressOfLeftShapeWord_left term sigma word .Z sample

/-- The marked coarse predicate on a relaxed address is precisely membership in the joint
split-type class. -/
theorem cwRecursiveMatchesAlpha_coarseAddressOfLeftShapeWord_iff
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (word : Fin (n + 1) → RecursiveChildShape
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth)) :
    CWRecursiveMatchesAlpha sigma alpha
        (cwRecursiveCoarseAddressOfLeftShapeWord term sigma word) ↔
      word ∈ alpha.markedWords := by
  unfold CWRecursiveMatchesAlpha
  rw [cwRecursiveLogicalLeftTripleWord_coarseAddressOfLeftShapeWord,
    alpha.multiplicity_coordinateTriple_comp_eq_coordinateTripleCount_iff]
  exact WordType.mem_typeClass.symm

/-- Each labelled occurrence of a relaxed quotient address obeys the tight child-total
equation. -/
theorem cwRecursiveCoarseAddressOfLeftShapeWord_coarse_sum
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (word : Fin (n + 1) → RecursiveChildShape
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth))
    (occurrence : Fin ((n + 1) + (n + 1))) :
    let address := cwRecursiveCoarseAddressOfLeftShapeWord term sigma word
    (address (sigma .X) occurrence : ℕ) +
        (address (sigma .Y) occurrence : ℕ) +
    (address (sigma .Z) occurrence : ℕ) = coarseTotal depth := by
  refine Fin.addCases ?_ ?_ occurrence <;> intro sample
  · simpa only [cwRecursiveCoarseAddressOfLeftShapeWord_left,
      ExactRecursiveSplitType.coordinate_val] using (word sample).total_eq
  · simpa only [cwRecursiveCoarseAddressOfLeftShapeWord_right,
      ExactRecursiveSplitType.coordinate_val] using
      ((RecursiveChildShape.complementPerm
        (cwRecursiveLogicalParent_total term sigma)) (word sample)).total_eq

/-- The left and right digits add to the fixed parent constituent coordinate on every physical
leg. -/
theorem cwRecursiveCoarseAddressOfLeftShapeWord_left_add_right
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (word : Fin (n + 1) → RecursiveChildShape
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth))
    (physicalLeg : Leg) (sample : Fin (n + 1)) :
    let address := cwRecursiveCoarseAddressOfLeftShapeWord term sigma word
    (address physicalLeg (Fin.castAdd (n + 1) sample) : ℕ) +
        (address physicalLeg (Fin.natAdd (n + 1) sample) : ℕ) =
      term.index.count physicalLeg := by
  let logicalLeg := sigma.symm physicalLeg
  have hphysical : sigma logicalLeg = physicalLeg := sigma.apply_symm_apply physicalLeg
  dsimp only
  rw [← hphysical, cwRecursiveCoarseAddressOfLeftShapeWord_left,
    cwRecursiveCoarseAddressOfLeftShapeWord_right]
  simpa only [ExactRecursiveSplitType.coordinate_val, cwRecursiveLogicalParent] using
    RecursiveChildShape.get_add_complement_get
      (cwRecursiveLogicalParent_total term sigma) (word sample) logicalLeg

/-- The complete relaxed ambient quotient support, in bijection with `N_triple`. -/
noncomputable def cwRecursiveRelaxedAmbientCoarseSupport
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Finset (CWRecursiveCoarseAddress depth n) := by
  classical
  exact alpha.marginalWords.image
    (cwRecursiveCoarseAddressOfLeftShapeWord term sigma)

/-- The relaxed marked quotient support, in bijection with `N_alpha`. -/
noncomputable def cwRecursiveRelaxedMarkedCoarseSupport
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Finset (CWRecursiveCoarseAddress depth n) := by
  classical
  exact alpha.markedWords.image
    (cwRecursiveCoarseAddressOfLeftShapeWord term sigma)

/-- The marked relaxed quotient family is contained in the ambient marginal family. -/
theorem cwRecursiveRelaxedMarkedCoarseSupport_subset_ambient
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    cwRecursiveRelaxedMarkedCoarseSupport term sigma alpha ⊆
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha := by
  classical
  exact Finset.image_mono _ alpha.markedWords_subset_marginalWords

/-- Every relaxed ambient quotient has the fixed parent coordinate total in each paired
left/right occurrence.  This is a property of the abstract quotient family itself and does not
require a fine lift in an exact or approximate parent interface. -/
theorem cwRecursiveRelaxedAmbientCoarseSupport_left_add_right
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n)
    (haddress : address ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (physicalLeg : Leg) (sample : Fin (n + 1)) :
    (address physicalLeg (Fin.castAdd (n + 1) sample) : ℕ) +
        (address physicalLeg (Fin.natAdd (n + 1) sample) : ℕ) =
      term.index.count physicalLeg := by
  classical
  rw [cwRecursiveRelaxedAmbientCoarseSupport, Finset.mem_image] at haddress
  obtain ⟨word, _hword, rfl⟩ := haddress
  exact cwRecursiveCoarseAddressOfLeftShapeWord_left_add_right
    term sigma word physicalLeg sample

/-- Same tagged ordered-left type gives a complete paired-position relabeling throughout the
relaxed ambient quotient family.  Unlike the older fine-support specialization, this theorem
also applies to intended hash targets whose approximate-parent preimage is empty. -/
theorem cwRecursivePositionRelabelCoarseAddress_of_relaxedAmbient_sameTaggedMultiplicity
    {Part : Type v} [Fintype Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (left right : CWRecursiveCoarseAddress depth n)
    (hleft : left ∈ cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (hright : right ∈ cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (htype : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma left) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma right)) :
    cwRecursivePositionRelabelCoarseAddress depth n
        (cwRecursivePositionPermOfSameTaggedMultiplicity
          partAt sigma left right htype) right = left := by
  apply
    cwRecursivePositionRelabelCoarseAddress_positionPermOfSameTaggedMultiplicity_of_totals
      partAt sigma term.index.count left right
  · exact fun physicalLeg sample ↦
      cwRecursiveRelaxedAmbientCoarseSupport_left_add_right
        term sigma alpha left hleft physicalLeg sample
  · exact fun physicalLeg sample ↦
      cwRecursiveRelaxedAmbientCoarseSupport_left_add_right
        term sigma alpha right hright physicalLeg sample

/-- Exact finite `N_triple` cardinality of the relaxed ambient coarse family. -/
@[simp] theorem card_cwRecursiveRelaxedAmbientCoarseSupport
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    (cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha).card =
      alpha.marginalWords.card := by
  classical
  exact Finset.card_image_of_injective _
    (cwRecursiveCoarseAddressOfLeftShapeWord_injective term sigma)

/-- Exact finite `N_alpha` cardinality of the relaxed marked coarse family. -/
@[simp] theorem card_cwRecursiveRelaxedMarkedCoarseSupport
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    (cwRecursiveRelaxedMarkedCoarseSupport term sigma alpha).card =
      Nat.multinomial Finset.univ alpha.count := by
  classical
  rw [cwRecursiveRelaxedMarkedCoarseSupport,
    Finset.card_image_of_injective _
      (cwRecursiveCoarseAddressOfLeftShapeWord_injective term sigma),
    alpha.card_markedWords]

/-! ## The approximate fine quotient maps into the relaxed family -/

/-- Recover the ordered-left child-shape word directly from one supported approximate quotient
address.  The right occurrence witnesses the coordinate bounds; tightness supplies the common
child total. -/
def cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n)
    (haddress : address ∈
      (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).support) :
    Fin (n + 1) → RecursiveChildShape
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) :=
  fun sample ↦ RecursiveChildShape.ofCoordinates
    (fun logicalLeg ↦
      (address (sigma logicalLeg) (Fin.castAdd (n + 1) sample) : ℕ))
    (fun logicalLeg ↦ by
      have hadd :=
        cwRecursiveApproximateCoarsenedAlphaMarginalTerm_left_add_right
          K q term hmultiplicity epsilon sigma alpha address haddress
            (sigma logicalLeg) sample
      change (address (sigma logicalLeg)
          (Fin.castAdd (n + 1) sample) : ℕ) ≤
        cwRecursiveLogicalParent term sigma logicalLeg
      simpa [cwRecursiveLogicalParent] using Nat.le.intro hadd)
    (by
      have hsum :=
        cwRecursiveApproximateCoarsenedAlphaMarginalTerm_coarse_sum
          K q term hmultiplicity epsilon sigma alpha address haddress
            (Fin.castAdd (n + 1) sample)
      have hperm :
          (∑ c : Leg,
            (address (sigma c) (Fin.castAdd (n + 1) sample) : ℕ)) =
          ∑ c : Leg,
            (address c (Fin.castAdd (n + 1) sample) : ℕ) :=
        Fintype.sum_equiv sigma _ _ (fun _ ↦ rfl)
      calc
        (address (sigma .X) (Fin.castAdd (n + 1) sample) : ℕ) +
            (address (sigma .Y) (Fin.castAdd (n + 1) sample) : ℕ) +
            (address (sigma .Z) (Fin.castAdd (n + 1) sample) : ℕ) =
          ∑ c : Leg,
            (address (sigma c) (Fin.castAdd (n + 1) sample) : ℕ) := by
              simp [Tensor.sum_leg]
        _ = ∑ c : Leg,
            (address c (Fin.castAdd (n + 1) sample) : ℕ) := hperm
        _ = coarseTotal depth := by
          simpa [Tensor.sum_leg] using hsum)

@[simp] theorem coordinate_cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
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
    (logicalLeg : Leg) (sample : Fin (n + 1)) :
    ExactRecursiveSplitType.coordinate logicalLeg
        (cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
          K q term hmultiplicity epsilon sigma alpha address haddress sample) =
      address (sigma logicalLeg) (Fin.castAdd (n + 1) sample) := by
  apply Fin.ext
  simp [cwRecursiveApproximateLogicalLeftShapeWordOfCoarse,
    ExactRecursiveSplitType.coordinate]

/-- The retained right occurrence is the complement of the recovered ordered-left shape. -/
theorem coordinate_complement_cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
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
    (logicalLeg : Leg) (sample : Fin (n + 1)) :
    ExactRecursiveSplitType.coordinate logicalLeg
        ((RecursiveChildShape.complementPerm
          (cwRecursiveLogicalParent_total term sigma))
          (cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
            K q term hmultiplicity epsilon sigma alpha address haddress sample)) =
      address (sigma logicalLeg) (Fin.natAdd (n + 1) sample) := by
  apply Fin.ext
  have hadd := cwRecursiveApproximateCoarsenedAlphaMarginalTerm_left_add_right
    K q term hmultiplicity epsilon sigma alpha address haddress
      (sigma logicalLeg) sample
  have hleft :
      (cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
        K q term hmultiplicity epsilon sigma alpha address haddress sample).get
          logicalLeg =
        (address (sigma logicalLeg) (Fin.castAdd (n + 1) sample) : ℕ) :=
    congrArg Fin.val
      (coordinate_cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
        K q term hmultiplicity epsilon sigma alpha address haddress
          logicalLeg sample)
  simp only [ExactRecursiveSplitType.coordinate_val,
    RecursiveChildShape.complementPerm_apply,
    RecursiveChildShape.complement_get]
  change cwRecursiveLogicalParent term sigma logicalLeg -
      (cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
        K q term hmultiplicity epsilon sigma alpha address haddress sample).get
          logicalLeg = _
  rw [hleft]
  change term.index.count (sigma logicalLeg) -
      (address (sigma logicalLeg) (Fin.castAdd (n + 1) sample) : ℕ) = _
  exact Nat.sub_eq_of_eq_add (by simpa [Nat.add_comm] using hadd.symm)

/-- Rebuilding a supported approximate quotient address from its recovered ordered-left shape is
the identity. -/
theorem cwRecursiveCoarseAddressOfLeftShapeWord_approximateShape_eq
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n)
    (haddress : address ∈
      (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).support) :
    cwRecursiveCoarseAddressOfLeftShapeWord term sigma
        (cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
          K q term hmultiplicity epsilon sigma alpha address haddress) = address := by
  funext physicalLeg occurrence
  let logicalLeg := sigma.symm physicalLeg
  have hphysical : sigma logicalLeg = physicalLeg := sigma.apply_symm_apply physicalLeg
  refine Fin.addCases ?_ ?_ occurrence <;> intro sample
  · rw [← hphysical, cwRecursiveCoarseAddressOfLeftShapeWord_left]
    exact coordinate_cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
      K q term hmultiplicity epsilon sigma alpha address haddress
        logicalLeg sample
  · rw [← hphysical, cwRecursiveCoarseAddressOfLeftShapeWord_right]
    exact coordinate_complement_cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
      K q term hmultiplicity epsilon sigma alpha address haddress
        logicalLeg sample

/-- The recovered ordered-left shape word has the three exact marginals imposed by `alpha`. -/
theorem cwRecursiveApproximateLogicalLeftShapeWordOfCoarse_mem_marginalWords
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n)
    (haddress : address ∈
      (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).support) :
    cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
        K q term hmultiplicity epsilon sigma alpha address haddress ∈
      alpha.marginalWords := by
  classical
  have horiginal := haddress
  rw [ExactRecursiveSplitType.mem_marginalWords]
  intro logicalLeg
  change address ∈
    ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).coarsen
        (cwRecursiveChildCoarsening depth n)).support at haddress
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hcoarse⟩ := haddress
  have hmarginal :=
    (mem_cwRecursiveApproximateAlphaMarginalSelectedTerm_support
      K q term hmultiplicity epsilon sigma alpha fine).mp hfine |>.2
        (sigma logicalLeg)
  calc
    WordType.multiplicity
        (ExactRecursiveSplitType.coordinateWord logicalLeg
          (cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
            K q term hmultiplicity epsilon sigma alpha address horiginal)) =
      WordType.multiplicity
        (cwRecursiveLogicalLeftCoordinateWord sigma address logicalLeg) := by
          congr 1
          funext sample
          exact coordinate_cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
            K q term hmultiplicity epsilon sigma alpha address
              horiginal logicalLeg sample
    _ = WordType.multiplicity
        (cwRecursiveLeftChildWord depth n (fine (sigma logicalLeg))) := by
      congr 1
      funext sample
      rw [← hcoarse]
      simp only [cwRecursiveLogicalLeftCoordinateWord, coarsenBlockAddress_apply,
        cwRecursiveChildCoarsening, cwRecursiveLabelledChildWord_left]
    _ = alpha.marginalCount logicalLeg := by
      simpa [sigma.symm_apply_apply] using hmarginal

/-- Every actual coarse quotient of the approximate alpha-selected tensor belongs to the relaxed
ambient hashing family. -/
theorem cwRecursiveApproximateCoarsened_support_subset_relaxedAmbient
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
      K q term hmultiplicity epsilon sigma alpha).support ⊆
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha := by
  classical
  intro address haddress
  unfold cwRecursiveRelaxedAmbientCoarseSupport
  apply Finset.mem_image.mpr
  refine ⟨cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
    K q term hmultiplicity epsilon sigma alpha address haddress, ?_, ?_⟩
  · exact cwRecursiveApproximateLogicalLeftShapeWordOfCoarse_mem_marginalWords
      K q term hmultiplicity epsilon sigma alpha address haddress
  · exact cwRecursiveCoarseAddressOfLeftShapeWord_approximateShape_eq
      K q term hmultiplicity epsilon sigma alpha address haddress

/-- An actual approximate quotient address satisfying the marked joint-type predicate belongs to
the full relaxed marked family. -/
theorem mem_cwRecursiveRelaxedMarkedCoarseSupport_of_approximate_of_matchesAlpha
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
    (hmarked : CWRecursiveMatchesAlpha sigma alpha address) :
    address ∈ cwRecursiveRelaxedMarkedCoarseSupport term sigma alpha := by
  classical
  let word := cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
    K q term hmultiplicity epsilon sigma alpha address haddress
  have hrebuild : cwRecursiveCoarseAddressOfLeftShapeWord term sigma word = address :=
    cwRecursiveCoarseAddressOfLeftShapeWord_approximateShape_eq
      K q term hmultiplicity epsilon sigma alpha address haddress
  have hword : word ∈ alpha.markedWords := by
    apply (cwRecursiveMatchesAlpha_coarseAddressOfLeftShapeWord_iff
      term sigma alpha word).mp
    simpa [hrebuild] using hmarked
  unfold cwRecursiveRelaxedMarkedCoarseSupport
  exact Finset.mem_image.mpr ⟨word, hword, hrebuild⟩

namespace CWCoarseFieldEncoding

variable {R : Type v} [Field R]

/-- Encode one relaxed recursive quotient address as the affine legal triple used by hashing. -/
def relaxedRecursiveOrientedLegalTriple
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (word : Fin (n + 1) → RecursiveChildShape
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth)) :
    ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target :=
  let address := cwRecursiveCoarseAddressOfLeftShapeWord term sigma word
  { xIndex := fun occurrence ↦ encoding.encode (address (sigma .X) occurrence)
    yIndex := fun occurrence ↦ encoding.encode (address (sigma .Y) occurrence)
    zIndex := fun occurrence ↦ encoding.encode (address (sigma .Z) occurrence)
    legal := fun occurrence ↦ encoding.legal_of_val_sum _ _ _
      (cwRecursiveCoarseAddressOfLeftShapeWord_coarse_sum
        term sigma word occurrence) }

/-- The relaxed legal-triple encoding loses no ordered child-shape word. -/
theorem relaxedRecursiveOrientedLegalTriple_injective
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation) :
    Function.Injective
      (encoding.relaxedRecursiveOrientedLegalTriple (n := n) term sigma) := by
  intro left right heq
  apply cwRecursiveCoarseAddressOfLeftShapeWord_injective term sigma
  funext physicalLeg occurrence
  let logicalLeg := sigma.symm physicalLeg
  have hphysical : sigma logicalLeg = physicalLeg := sigma.apply_symm_apply physicalLeg
  rw [← hphysical]
  apply encoding.encode_injective
  cases logicalLeg with
  | X =>
      simpa [relaxedRecursiveOrientedLegalTriple] using
        congrFun (congrArg ProgressionHash.LegalTriple.xIndex heq) occurrence
  | Y =>
      simpa [relaxedRecursiveOrientedLegalTriple] using
        congrFun (congrArg ProgressionHash.LegalTriple.yIndex heq) occurrence
  | Z =>
      simpa [relaxedRecursiveOrientedLegalTriple] using
        congrFun (congrArg ProgressionHash.LegalTriple.zIndex heq) occurrence

/-- Relaxed ambient legal targets. -/
noncomputable def relaxedRecursiveAmbientTargets
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Finset (ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target) := by
  classical
  exact alpha.marginalWords.image
    (encoding.relaxedRecursiveOrientedLegalTriple term sigma)

/-- Relaxed marked legal targets. -/
noncomputable def relaxedRecursiveMarkedTargets
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Finset (ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target) := by
  classical
  exact alpha.markedWords.image
    (encoding.relaxedRecursiveOrientedLegalTriple term sigma)

/-- Every relaxed marked legal target is ambient. -/
theorem relaxedRecursiveMarkedTargets_subset_ambientTargets
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    encoding.relaxedRecursiveMarkedTargets term sigma alpha ⊆
      encoding.relaxedRecursiveAmbientTargets term sigma alpha := by
  classical
  exact Finset.image_mono _ alpha.markedWords_subset_marginalWords

/-- The legal marked family has exactly the paper's finite `N_alpha` count. -/
@[simp] theorem card_relaxedRecursiveMarkedTargets
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    (encoding.relaxedRecursiveMarkedTargets term sigma alpha).card =
      Nat.multinomial Finset.univ alpha.count := by
  classical
  rw [relaxedRecursiveMarkedTargets,
    Finset.card_image_of_injective _
      (encoding.relaxedRecursiveOrientedLegalTriple_injective term sigma),
    alpha.card_markedWords]

/-- The legal ambient family has exactly the paper's finite `N_triple` count. -/
@[simp] theorem card_relaxedRecursiveAmbientTargets
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    (encoding.relaxedRecursiveAmbientTargets term sigma alpha).card =
      alpha.marginalWords.card := by
  classical
  exact Finset.card_image_of_injective _
    (encoding.relaxedRecursiveOrientedLegalTriple_injective term sigma)

/-- The injective relaxed legal-triple representation is an equivalence onto the ambient target
family. -/
noncomputable def relaxedRecursiveAmbientTargetEquiv
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    {word // word ∈ alpha.marginalWords} ≃
      {triple : ProgressionHash.LegalTriple R
          (Fin ((n + 1) + (n + 1))) encoding.target //
        triple ∈ encoding.relaxedRecursiveAmbientTargets term sigma alpha} := by
  classical
  let f := fun source : {word // word ∈ alpha.marginalWords} ↦
    (⟨encoding.relaxedRecursiveOrientedLegalTriple term sigma source.1,
      Finset.mem_image.mpr ⟨source.1, source.2, rfl⟩⟩ :
      {triple : ProgressionHash.LegalTriple R
          (Fin ((n + 1) + (n + 1))) encoding.target //
        triple ∈ encoding.relaxedRecursiveAmbientTargets term sigma alpha})
  apply Equiv.ofBijective f
  constructor
  · intro left right heq
    apply Subtype.ext
    exact encoding.relaxedRecursiveOrientedLegalTriple_injective term sigma
      (congrArg Subtype.val heq)
  · intro target
    have htarget := target.2
    change target.1 ∈ Finset.image
      (encoding.relaxedRecursiveOrientedLegalTriple term sigma) alpha.marginalWords at htarget
    rw [Finset.mem_image] at htarget
    obtain ⟨word, hword, hvalue⟩ := htarget
    refine ⟨⟨word, hword⟩, ?_⟩
    apply Subtype.ext
    exact hvalue

/-- Recover the abstract ordered-left shape word represented by one ambient legal target. -/
noncomputable def relaxedRecursiveAmbientSourceOfTarget
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (target : {triple : ProgressionHash.LegalTriple R
        (Fin ((n + 1) + (n + 1))) encoding.target //
      triple ∈ encoding.relaxedRecursiveAmbientTargets term sigma alpha}) :=
  (encoding.relaxedRecursiveAmbientTargetEquiv term sigma alpha).symm target

@[simp] theorem relaxedRecursiveOrientedLegalTriple_ambientSourceOfTarget
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (target : {triple : ProgressionHash.LegalTriple R
        (Fin ((n + 1) + (n + 1))) encoding.target //
      triple ∈ encoding.relaxedRecursiveAmbientTargets term sigma alpha}) :
    encoding.relaxedRecursiveOrientedLegalTriple term sigma
        (encoding.relaxedRecursiveAmbientSourceOfTarget
          term sigma alpha target).1 = target.1 := by
  exact congrArg Subtype.val
    ((encoding.relaxedRecursiveAmbientTargetEquiv
      term sigma alpha).apply_symm_apply target)

/-- Every relaxed ambient `X`-competitor fiber injects into the corresponding abstract
marginal-word fiber.  In fact the two sets have the same size, but this one-sided form is exactly
what affine hashing consumes. -/
theorem card_relaxedRecursiveAmbient_xFiber_le_marginalWordFiber
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {word // word ∈ alpha.marginalWords}) :
    (ProgressionHash.LegalTriple.xFiber
      (encoding.relaxedRecursiveAmbientTargets term sigma alpha)
      (encoding.relaxedRecursiveOrientedLegalTriple
        term sigma source.1)).card ≤
      (alpha.marginalWordFiber .X
        (ExactRecursiveSplitType.coordinateWord .X source.1)).card := by
  classical
  let ambient := encoding.relaxedRecursiveAmbientTargets term sigma alpha
  let chosen := encoding.relaxedRecursiveOrientedLegalTriple term sigma source.1
  let fiber := ProgressionHash.LegalTriple.xFiber ambient chosen
  let sourceOf := fun other : {triple : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target // triple ∈ ambient} ↦
    encoding.relaxedRecursiveAmbientSourceOfTarget term sigma alpha other
  let shapeOf := fun other : {triple : ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target // triple ∈ fiber} ↦
    let hambient : other.1 ∈ ambient := (Finset.mem_filter.mp other.2).1
    (sourceOf ⟨other.1, hambient⟩).1
  have hbound : fiber.attach.card ≤
      (alpha.marginalWordFiber .X
        (ExactRecursiveSplitType.coordinateWord .X source.1)).card := by
    apply Finset.card_le_card_of_injOn shapeOf
    · intro other _hother
      have hother : other.1 ∈ ambient ∧ other.1.xIndex = chosen.xIndex :=
        Finset.mem_filter.mp other.2
      let otherSource := sourceOf ⟨other.1, hother.1⟩
      apply (ExactRecursiveSplitType.mem_marginalWordFiber
        alpha .X (ExactRecursiveSplitType.coordinateWord .X source.1)
          (shapeOf other)).2
      refine ⟨otherSource.2, ?_⟩
      funext sample
      apply encoding.encode_injective
      have hx := congrFun hother.2 (Fin.castAdd (n + 1) sample)
      have hsourceTriple :=
        encoding.relaxedRecursiveOrientedLegalTriple_ambientSourceOfTarget
          term sigma alpha ⟨other.1, hother.1⟩
      have hxSource := congrFun
        (congrArg ProgressionHash.LegalTriple.xIndex hsourceTriple)
        (Fin.castAdd (n + 1) sample)
      simpa [shapeOf, sourceOf, otherSource, chosen,
        relaxedRecursiveOrientedLegalTriple,
        ExactRecursiveSplitType.coordinateWord, Function.comp_apply] using hxSource.trans hx
    · intro left _hleft right _hright heq
      have hleft : left.1 ∈ ambient := (Finset.mem_filter.mp left.2).1
      have hright : right.1 ∈ ambient := (Finset.mem_filter.mp right.2).1
      let leftSource := sourceOf ⟨left.1, hleft⟩
      let rightSource := sourceOf ⟨right.1, hright⟩
      have hsource : leftSource = rightSource := by
        apply Subtype.ext
        simpa [shapeOf, sourceOf, leftSource, rightSource] using heq
      apply Subtype.ext
      calc
        left.1 = encoding.relaxedRecursiveOrientedLegalTriple
            term sigma leftSource.1 := by
          change left.1 = encoding.relaxedRecursiveOrientedLegalTriple term sigma
            (encoding.relaxedRecursiveAmbientSourceOfTarget
              term sigma alpha ⟨left.1, hleft⟩).1
          exact (encoding.relaxedRecursiveOrientedLegalTriple_ambientSourceOfTarget
            term sigma alpha ⟨left.1, hleft⟩).symm
        _ = encoding.relaxedRecursiveOrientedLegalTriple
            term sigma rightSource.1 := congrArg _ (congrArg Subtype.val hsource)
        _ = right.1 := by
          change encoding.relaxedRecursiveOrientedLegalTriple term sigma
            (encoding.relaxedRecursiveAmbientSourceOfTarget
              term sigma alpha ⟨right.1, hright⟩).1 = right.1
          exact encoding.relaxedRecursiveOrientedLegalTriple_ambientSourceOfTarget
            term sigma alpha ⟨right.1, hright⟩
  simpa [fiber] using hbound

/-- Division-free paper form of the exact relaxed competitor degree estimate:
`N_X * degree_X ≤ N_triple`. -/
theorem card_coordinateType_mul_card_relaxedRecursiveAmbient_xFiber_le
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {word // word ∈ alpha.marginalWords}) :
    (WordType.typeClass (n + 1) (alpha.marginalCount .X)).card *
        (ProgressionHash.LegalTriple.xFiber
          (encoding.relaxedRecursiveAmbientTargets term sigma alpha)
          (encoding.relaxedRecursiveOrientedLegalTriple
            term sigma source.1)).card ≤
      alpha.marginalWords.card := by
  have htarget : ExactRecursiveSplitType.coordinateWord .X source.1 ∈
      WordType.typeClass (n + 1) (alpha.marginalCount .X) := by
    rw [WordType.mem_typeClass]
    exact (ExactRecursiveSplitType.mem_marginalWords alpha source.1).mp source.2 .X
  calc
    _ ≤ (WordType.typeClass (n + 1) (alpha.marginalCount .X)).card *
        (alpha.marginalWordFiber .X
          (ExactRecursiveSplitType.coordinateWord .X source.1)).card :=
      Nat.mul_le_mul_left _
        (encoding.card_relaxedRecursiveAmbient_xFiber_le_marginalWordFiber
          term sigma alpha source)
    _ = alpha.marginalWords.card :=
      alpha.card_coordinateType_mul_card_marginalWordFiber .X _ htarget

end CWCoarseFieldEncoding

end AlgebraicComplexity.Examples
