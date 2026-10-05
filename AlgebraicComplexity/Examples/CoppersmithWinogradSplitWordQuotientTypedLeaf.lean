import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordQuotient
import AlgebraicComplexity.MatrixMultiplication.CoarsenedRationalTypedLeaf

/-!
# Fine leaves under the level-two CW reversal quotient

This file closes the finite joint-type issue for the globally consistent quotient which sorts
each two-digit complete-split word.  Fixing only the three unconditional quotient marginals is
not enough in general.  The recursive CW input is stronger: it fixes the ordered child shape
(`alpha`) and the quotient profile on every leg conditional on that shape.

For the depth-one CW support, inside every fixed shape fiber one quotient coordinate is
injective.  Hence the three shape-conditional profiles determine the full quotient joint type.
This includes the zero shapes.  Combined with the paper-independent coarse-to-fine theorem, a
family of extracted coarse constituents therefore yields the same number of fine rational typed
leaves, with unchanged matrix dimensions and with no extra conditional-entropy charge.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-- A fine level-two CW support letter is an ordered pair of supported base constituents. -/
abbrev CWSortedPairFineLetter := PositiveWord cwBlockSupport 1

/-- Apply the globally consistent pair-sorting quotient to all three labels of a fine level-two
support letter. -/
def cwSortedPairCoarseAddressOfFine (word : CWSortedPairFineLetter) :
    BlockAddress (fun _c ↦ SplitWord 1) :=
  coarsenBlockAddress cwSortedPairChunkCoarsening
    (positiveSupportWordBlockAddress cwBlockSupport 1 word)

/-- Ordered level-two shape (the three total digit weights) of a quotient address. -/
def cwSortedPairCoarseShape
    (address : BlockAddress (fun _c ↦ SplitWord 1)) : Leg → ℕ :=
  fun c ↦ splitWordWeight (address c)

/-- A coordinate which separates the quotient addresses in a fixed supported shape fiber.  A
total-two coordinate is used whenever present; all fibers without one are singletons. -/
def cwSortedPairRigidityLeg (shape : Leg → ℕ) : Leg :=
  if shape .X = 2 then .X else if shape .Y = 2 then .Y else .Z

/-- Finite depth-one CW calculation: equal shapes and equality on the selected coordinate force
equality of the two globally sorted quotient addresses.  Kernel reduction checks the 36 by 36
ordered pairs of supported base constituents; no native-decision axiom is used. -/
theorem cwSortedPairCoarseAddressOfFine_eq_of_shape_and_rigidityLeg
    (left right : CWSortedPairFineLetter)
    (hshape : cwSortedPairCoarseShape (cwSortedPairCoarseAddressOfFine left) =
      cwSortedPairCoarseShape (cwSortedPairCoarseAddressOfFine right))
    (hcoordinate :
      cwSortedPairCoarseAddressOfFine left
          (cwSortedPairRigidityLeg
            (cwSortedPairCoarseShape (cwSortedPairCoarseAddressOfFine left))) =
        cwSortedPairCoarseAddressOfFine right
          (cwSortedPairRigidityLeg
            (cwSortedPairCoarseShape (cwSortedPairCoarseAddressOfFine left)))) :
    cwSortedPairCoarseAddressOfFine left =
      cwSortedPairCoarseAddressOfFine right := by
  decide +revert

section TensorSupport

variable (K : Type u) [CommRing K] (q : ℕ)

/-- The actual finite quotient support used by the level-two tensor partition. -/
noncomputable abbrev CWSortedPairCoarseSupport :=
  ((cwChunkPartitionedTensor K q 1).coarsen cwSortedPairChunkCoarsening).support

/-- Shape of an actual supported quotient address. -/
def cwSortedPairSupportedShape
    (address : CWSortedPairCoarseSupport K q) : Leg → ℕ :=
  cwSortedPairCoarseShape address.1

/-- Every actual supported quotient address has a fine ordered-pair representative. -/
theorem exists_cwSortedPairFineLetter
    (address : CWSortedPairCoarseSupport K q) :
    ∃ word : CWSortedPairFineLetter,
      cwSortedPairCoarseAddressOfFine word = address.1 := by
  have haddress := address.property
  change address.1 ∈
    ((cwChunkPartitionedTensor K q 1).coarsen
      cwSortedPairChunkCoarsening).support at haddress
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨source, hsource, hsourceMap⟩ := haddress
  change source ∈ ((cwPartitionedTensor K q).positivePower 1).support at hsource
  obtain ⟨word, hword⟩ :=
    (cwPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support
      1 hsource
  let fineWord : CWSortedPairFineLetter := word
  refine ⟨fineWord, ?_⟩
  unfold cwSortedPairCoarseAddressOfFine
  have hword' :
      positiveSupportWordBlockAddress cwBlockSupport 1 fineWord = source := by
    simpa [fineWord, cwPartitionedTensor] using hword
  rw [hword']
  exact hsourceMap

/-- Within every fixed ordered level-two shape, one coordinate projection is injective on the
actual pair-sorted CW quotient support.  This statement covers both positive and zero shapes. -/
theorem cwSortedPairCoarseSupport_conditionallyCoordinateInjective :
    ∀ shape : Leg → ℕ,
      ∃ c, Set.InjOn (fun address : CWSortedPairCoarseSupport K q ↦ address.1 c)
        {address | cwSortedPairSupportedShape K q address = shape} := by
  intro shape
  refine ⟨cwSortedPairRigidityLeg shape, ?_⟩
  intro left hleft right hright hcoordinate
  obtain ⟨leftWord, hleftWord⟩ := exists_cwSortedPairFineLetter K q left
  obtain ⟨rightWord, hrightWord⟩ := exists_cwSortedPairFineLetter K q right
  change cwSortedPairSupportedShape K q left = shape at hleft
  change cwSortedPairSupportedShape K q right = shape at hright
  apply Subtype.ext
  rw [← hleftWord, ← hrightWord]
  apply cwSortedPairCoarseAddressOfFine_eq_of_shape_and_rigidityLeg
  · have hleftShape :
        cwSortedPairCoarseShape (cwSortedPairCoarseAddressOfFine leftWord) = shape := by
      simpa [cwSortedPairSupportedShape, hleftWord] using hleft
    have hrightShape :
        cwSortedPairCoarseShape (cwSortedPairCoarseAddressOfFine rightWord) = shape := by
      simpa [cwSortedPairSupportedShape, hrightWord] using hright
    exact hleftShape.trans hrightShape.symm
  · have hleftShape :
        cwSortedPairCoarseShape (cwSortedPairCoarseAddressOfFine leftWord) = shape := by
      simpa [cwSortedPairSupportedShape, hleftWord] using hleft
    have hleg : cwSortedPairRigidityLeg
        (cwSortedPairCoarseShape (cwSortedPairCoarseAddressOfFine leftWord)) =
        cwSortedPairRigidityLeg shape := by
      exact congrArg cwSortedPairRigidityLeg hleftShape
    rw [hleg, hleftWord, hrightWord]
    exact hcoordinate

/-- Fixed `alpha` together with all shape-conditional quotient profiles uniquely determines the
full joint type on the actual level-two pair-sorted support. -/
theorem cwSortedPair_jointType_eq_of_conditionalProfiles
    (p qtype : CWSortedPairCoarseSupport K q → ℕ)
    (hprofiles : ∀ c,
      WordType.mappedType
          (fun address : CWSortedPairCoarseSupport K q ↦
            (cwSortedPairSupportedShape K q address, address.1 c)) p =
        WordType.mappedType
          (fun address : CWSortedPairCoarseSupport K q ↦
            (cwSortedPairSupportedShape K q address, address.1 c)) qtype) :
    p = qtype :=
  WordType.jointType_eq_of_conditionally_injective_coordinate
    (cwSortedPairSupportedShape K q) (fun c address ↦ address.1 c)
    (cwSortedPairCoarseSupport_conditionallyCoordinateInjective K q)
    p qtype hprofiles

/-- The full type-selected tensor for the globally pair-sorted level-two partition restricts
back to the **entire** original fine type-selected tensor.  Thus every already-separated outer
copy retains the original inner `E2` type-class exponent and matrix-dimension calculation.  The
outer copy count and `E2` are hierarchical multiplicative factors, not two counts of lifts at
the same scale.  The statement applies uniformly to positive and zero constituent types. -/
theorem cwSortedPair_coarseSelectedTypes_restricts_fineSelectedTypes
    (n : ℕ)
    (fineType : ∀ c, PositiveWord CWBlock 1 → ℕ) :
    Restricts
      (((((cwChunkPartitionedTensor K q 1).positivePower n).coarsen
          (fun c ↦ positiveWordMap (cwSortedPairChunkCoarsening c) n)).select
        (fun c word ↦ word ∈ positiveTypeClass (SplitWord 1) n
          (WordType.mappedType (cwSortedPairChunkCoarsening c) (fineType c)))).realize)
      ((((cwChunkPartitionedTensor K q 1).positivePower n).select
        (fun c word ↦ word ∈ positiveTypeClass (PositiveWord CWBlock 1) n
          (fineType c))).realize) :=
  Restricts.coarsenedPositivePowerSelectMappedTypes_to_fineTypes
    (cwChunkPartitionedTensor K q 1) cwSortedPairChunkCoarsening n fineType

/-- Indexed copy-preserving specialization: the outer family index is unchanged and each copy
still contains the whole original fine type-selected tensor. -/
theorem cwSortedPair_indexedDirectSum_coarseSelectedTypes_restricts_fineSelectedTypes
    {I : Type*} [Fintype I]
    (n : ℕ)
    (fineType : ∀ c, PositiveWord CWBlock 1 → ℕ) :
    Restricts
      (Tensor.indexedDirectSum (fun _i : I ↦
        ((((cwChunkPartitionedTensor K q 1).positivePower n).coarsen
          (fun c ↦ positiveWordMap (cwSortedPairChunkCoarsening c) n)).select
            (fun c word ↦ word ∈ positiveTypeClass (SplitWord 1) n
              (WordType.mappedType (cwSortedPairChunkCoarsening c) (fineType c)))).realize))
      (Tensor.indexedDirectSum (fun _i : I ↦
        (((cwChunkPartitionedTensor K q 1).positivePower n).select
          (fun c word ↦ word ∈ positiveTypeClass (PositiveWord CWBlock 1) n
            (fineType c))).realize)) :=
  Restricts.indexedDirectSum_coarsenedPositivePowerSelectMappedTypes_to_fineTypes
    (I := I) (cwChunkPartitionedTensor K q 1) cwSortedPairChunkCoarsening n fineType

end TensorSupport

/-! The coarse-to-fine typed-leaf and indexed copy-preservation theorems are
`RationalTypedLeaf.coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType` and
`RationalTypedLeaf.indexedDirectSum_coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType`.
The theorem above supplies their full-joint-type premise from the exact level-two recursive
tables. -/

end AlgebraicComplexity.Examples
