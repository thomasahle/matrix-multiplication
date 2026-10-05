import MatrixMultiplication.CW112LeafEvaluator
import MatrixMultiplication.SimplifiedExponentRecurrence

/-!
# Active sparse level-two entries as CW `112` typed leaves

The simplified level-four certificate stores its active level-two `mu` parameters at denominator
`2^12`.  This module connects those concrete sparse-table entries to the rational typed-leaf API.
It proves that the evaluator's retained-entropy term is the oriented CW `112` entropy and that its
positive volume term is the occurrence-weighted sum of the three logarithmic matrix dimensions.

The only generated support check says that every nonzero stored `mu` names a genuine positive
slot.  The strict interval `mu ∈ (0,1/2)` then follows abstractly from the sparse chunk's checked
validity invariant.  This bridge is intentionally opt-in; all analytic and tensor statements are
ordinary reusable theorems.
-/

open scoped BigOperators

namespace MatrixMultiplication.Generated.SimplifiedCW112Leaves

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData
open MatrixMultiplication.CW112LeafEvaluator
open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.SimplifiedExponentRecurrence

noncomputable section

/-- Half of the active certificate's 12-bit local denominator. -/
def halfDenominator : ℕ := 2 ^ (localBits - 1)

/-- Integral `G` count completing a stored numerator to half the local denominator. -/
def leafG (numerator : ℕ) : ℕ := halfDenominator - numerator

/-- A stored numerator below one half gives a positive complementary count. -/
theorem leafG_pos {numerator : ℕ} (hhalf : numerator < halfDenominator) :
    0 < leafG numerator :=
  Nat.sub_pos_of_lt hhalf

/-- The CW parameter reconstructed from the active 12-bit entry is exactly its dyadic mass.

Proof sketch: the two integral counts sum to `2^11`, hence `2(L+G)=2^12`. -/
theorem cw112Mu_numerator_leafG_eq_mass
    {numerator : ℕ} (hhalf : numerator < halfDenominator) :
    cw112Mu numerator (leafG numerator) = mass localBits numerator := by
  have hsum : numerator + (halfDenominator - numerator) = halfDenominator :=
    Nat.add_sub_of_le (Nat.le_of_lt hhalf)
  unfold cw112Mu leafG mass
  rw [hsum]
  norm_num [halfDenominator, localBits]

/-- The evaluator's middle ternary mass is exactly `1-2*mu`. -/
theorem middleMass_eq
    {numerator : ℕ} (hhalf : numerator < halfDenominator) :
    mass localBits (2 ^ localBits - 2 * numerator) =
      1 - 2 * mass localBits numerator := by
  have hle : 2 * numerator ≤ 2 ^ localBits := by
    norm_num [halfDenominator, localBits] at hhalf ⊢
    omega
  unfold mass
  rw [Nat.cast_sub hle]
  push_cast
  norm_num [localBits]
  ring

/-- The exact entropy expression used by the sparse evaluator is the CW ternary entropy for the
integral profile `(L,L,G,G)=(numerator,numerator,2^11-numerator,2^11-numerator)`.

Proof sketch: expand the three dyadic Shannon summands and replace the middle mass by
`1-2*mu`; the two equal outer summands combine into the factor two. -/
theorem cw112MuEntropyBits_numerator_leafG_eq
    {numerator : ℕ} (hhalf : numerator < halfDenominator) :
    cw112MuEntropyBits numerator (leafG numerator) =
      positiveEdgeEntropyFromNumerator numerator := by
  unfold cw112MuEntropyBits positiveEdgeEntropyFromNumerator entropyTerm
  rw [cw112Mu_numerator_leafG_eq_mass hhalf, middleMass_eq hhalf]
  ring

/-- The oriented typed-leaf entropy vector is exactly the branch-local vector used by the active
retained-exponent recurrence. -/
theorem orientedRetainedRateBits_eq_evaluator
    (numerator : ℕ) (hnumerator : 0 < numerator)
    (hhalf : numerator < halfDenominator) (heavy coordinate : Fin 3) :
    orientedRetainedRateBits 5 numerator (leafG numerator) (by decide)
        hnumerator (leafG_pos hhalf) heavy coordinate =
      if coordinate = heavy then positiveEdgeEntropyFromNumerator numerator else 1 := by
  rw [orientedRetainedRateBits_eq]
  rw [cw112MuEntropyBits_numerator_leafG_eq hhalf]
  rfl

/-- The three logarithmic dimensions of the active CW leaf sum to the positive-edge volume
coefficient used by the evaluator. -/
theorem sum_dimensionRateBits_eq_evaluator
    (numerator : ℕ) (hnumerator : 0 < numerator)
    (hhalf : numerator < halfDenominator) :
    (∑ c, (cw112RationalTypedLeaf 5 numerator (leafG numerator)
        (by decide) hnumerator (leafG_pos hhalf)).dimensionRateBits c) =
      (2 - 2 * mass localBits numerator) *
        MatrixMultiplication.SimplifiedVolumeReconstruction.log2Nat 5 := by
  rw [cw112RationalTypedLeaf_sum_dimensionRateBits]
  rw [cw112Mu_numerator_leafG_eq_mass hhalf]
  rfl

/-- After multiplying by its occurrence mass, the typed leaf's total logarithmic dimension is
the active volume recurrence's positive-edge value. -/
theorem weighted_sum_dimensionRateBits_eq_evaluator
    (occurrence numerator : ℕ) (hnumerator : 0 < numerator)
    (hhalf : numerator < halfDenominator) :
    mass levelTwoOccurrenceBits occurrence *
        (∑ c, (cw112RationalTypedLeaf 5 numerator (leafG numerator)
          (by decide) hnumerator (leafG_pos hhalf)).dimensionRateBits c) =
      MatrixMultiplication.SimplifiedVolumeReconstruction.weightedPositiveEdgeValue
        levelTwoOccurrenceBits localBits occurrence numerator := by
  rw [sum_dimensionRateBits_eq_evaluator numerator hnumerator hhalf]
  unfold MatrixMultiplication.SimplifiedVolumeReconstruction.weightedPositiveEdgeValue
  ring

/-- Semantic package for one active sparse level-two entry. -/
def InstantiatesCW112TypedLeaf
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount) : Prop :=
  let numerator := muNumerator node region slot
  let occurrence := levelTwoOccurrenceNumerator node region slot
  let heavy := levelTwoHeavyCoordinate (splitShape node slot)
  splitSlotValid node slot ∧ (splitShape node slot).IsPositive ∧
    shapeCoordinate (splitShape node slot) heavy = 2 ∧
    (∀ c, c ≠ heavy → shapeCoordinate (splitShape node slot) c = 1) ∧
    ∃ (hnumerator : 0 < numerator) (hG : 0 < leafG numerator),
      cw112Mu numerator (leafG numerator) = mass localBits numerator ∧
      (∀ coordinate,
        levelTwoEntryRate node region slot coordinate =
          mass levelTwoOccurrenceBits occurrence *
            orientedRetainedRateBits 5 numerator (leafG numerator) (by decide)
              hnumerator hG heavy coordinate) ∧
      mass levelTwoOccurrenceBits occurrence *
          (∑ c, (cw112RationalTypedLeaf 5 numerator (leafG numerator)
            (by decide) hnumerator hG).dimensionRateBits c) =
        MatrixMultiplication.SimplifiedVolumeReconstruction.weightedPositiveEdgeValue
          levelTwoOccurrenceBits localBits occurrence numerator

/-- The analytic typed-leaf package follows from positivity and the strict half-denominator
bound on a selected sparse entry.

Proof sketch: the preceding identities identify μ, the oriented entropy branch, and the summed
dimensions.  The evaluator's entry definition only adds the common occurrence-mass factor. -/
theorem instantiates_cw112_of_bounds
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount)
    (hslot : splitSlotValid node slot ∧ (splitShape node slot).IsPositive)
    (hnumerator : 0 < muNumerator node region slot)
    (hhalf : muNumerator node region slot < halfDenominator) :
    InstantiatesCW112TypedLeaf node region slot := by
  unfold InstantiatesCW112TypedLeaf
  dsimp only
  let hG := leafG_pos hhalf
  have htotal := (splitShape_geometry node slot hslot.1).1
  refine ⟨hslot.1, hslot.2, ?_, ?_, hnumerator, hG,
    cw112Mu_numerator_leafG_eq_mass hhalf, ?_, ?_⟩
  · exact shapeCoordinate_heavyCoordinate_eq_two hslot.2 htotal
  · intro c hc
    exact shapeCoordinate_eq_one_of_ne_heavyCoordinate hslot.2 htotal c hc
  · intro coordinate
    rw [orientedRetainedRateBits_eq_evaluator _ hnumerator hhalf]
    unfold levelTwoEntryRate
    dsimp only
  · exact weighted_sum_dimensionRateBits_eq_evaluator _ _ hnumerator hhalf

/-! ## Sparse generated support -/

private theorem zipLookup_ne_zero_index_mem
    (indices values : List ℕ) (target : ℕ)
    (h : zipLookup indices values target ≠ 0) : target ∈ indices := by
  induction indices generalizing values with
  | nil => simp [zipLookup] at h
  | cons index indices ih =>
      cases values with
      | nil => simp [zipLookup] at h
      | cons value values =>
          by_cases hit : index = target
          · subst index
            simp
          · simp only [zipLookup, hit, if_false] at h
            exact List.mem_cons_of_mem index (ih values h)

private theorem zipLookup_ne_zero_value_mem
    (indices values : List ℕ) (target : ℕ)
    (h : zipLookup indices values target ≠ 0) :
    zipLookup indices values target ∈ values := by
  induction indices generalizing values with
  | nil => simp [zipLookup] at h
  | cons index indices ih =>
      cases values with
      | nil => simp [zipLookup] at h
      | cons value values =>
          by_cases hit : index = target
          · simp [zipLookup, hit]
          · simp only [zipLookup, hit, if_false] at h ⊢
            exact List.mem_cons_of_mem value (ih values h)

private theorem muNumerator_eq_zipLookup
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount) :
    muNumerator node region slot =
      zipLookup
        MatrixMultiplication.Generated.SimplifiedVolume.MuData0.data.scalarIndices.toList
        MatrixMultiplication.Generated.SimplifiedVolume.MuData0.data.numerators.toList
        (muFlatIndex node region slot) := by
  unfold muNumerator scalarNumeratorAt
    MatrixMultiplication.Generated.SimplifiedVolume.muChunks sparseScalarNumeratorAt
  simp

/-- Every sparse `mu` index names a genuine positive level-two slot.  This checks only the 953
stored indices, rather than reducing the full recurrence at all 7,560 padded locations. -/
theorem storedMuIndices_are_positiveSlots :
    MatrixMultiplication.Generated.SimplifiedVolume.MuData0.data.scalarIndices.toList.Forall
      fun edge =>
        MatrixMultiplication.SimplifiedVolumeReconstruction.splitSlotIsValid
            (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeNode edge)
            (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeSlot edge) = true ∧
          (MatrixMultiplication.SimplifiedVolumeReconstruction.splitShapeAt
            (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeNode edge)
            (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeSlot edge)).IsPositive := by
  rw [MatrixMultiplication.Generated.SimplifiedVolume.MuData0.data_eq_rawData]
  set_option maxRecDepth 100000 in
    decide

private theorem edgeNode_muFlatIndex
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount) :
    MatrixMultiplication.SimplifiedVolumeReconstruction.edgeNode
        (muFlatIndex node region slot) = node.val := by
  unfold MatrixMultiplication.SimplifiedVolumeReconstruction.edgeNode muFlatIndex
  have hregion := region.isLt
  have hslot := slot.isLt
  norm_num [regionCount, splitSlotCount] at hregion hslot ⊢
  omega

private theorem edgeSlot_muFlatIndex
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount) :
    MatrixMultiplication.SimplifiedVolumeReconstruction.edgeSlot
        (muFlatIndex node region slot) = slot.val := by
  unfold MatrixMultiplication.SimplifiedVolumeReconstruction.edgeSlot muFlatIndex
  have hregion := region.isLt
  have hslot := slot.isLt
  norm_num [regionCount, splitSlotCount] at hregion hslot ⊢
  omega

private theorem splitShapeAt_muFlatIndex
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount) :
    MatrixMultiplication.SimplifiedVolumeReconstruction.splitShapeAt
        (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeNode
          (muFlatIndex node region slot))
        (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeSlot
          (muFlatIndex node region slot)) = splitShape node slot := by
  rw [edgeNode_muFlatIndex, edgeSlot_muFlatIndex]
  unfold MatrixMultiplication.SimplifiedVolumeReconstruction.splitShapeAt splitShape
    MatrixMultiplication.SimplifiedVolumeReconstruction.nodeShapeAt nodeShape
  rfl

private theorem splitSlotIsValid_muFlatIndex_iff
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount) :
    MatrixMultiplication.SimplifiedVolumeReconstruction.splitSlotIsValid
        (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeNode
          (muFlatIndex node region slot))
        (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeSlot
          (muFlatIndex node region slot)) = true ↔ splitSlotValid node slot := by
  rw [edgeNode_muFlatIndex, edgeSlot_muFlatIndex]
  simp only [MatrixMultiplication.SimplifiedVolumeReconstruction.splitSlotIsValid,
    decide_eq_true_eq]
  unfold splitSlotValid MatrixMultiplication.SimplifiedVolumeReconstruction.nodeShapeAt nodeShape
  rfl

/-- A nonzero stored `mu` value necessarily belongs to a valid positive `(1,1,2)` slot. -/
theorem selected_mu_positiveSlot
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount)
    (hselected : 0 < muNumerator node region slot) :
    splitSlotValid node slot ∧ (splitShape node slot).IsPositive := by
  have hlookup :
      zipLookup
        MatrixMultiplication.Generated.SimplifiedVolume.MuData0.data.scalarIndices.toList
        MatrixMultiplication.Generated.SimplifiedVolume.MuData0.data.numerators.toList
        (muFlatIndex node region slot) ≠ 0 := by
    rw [← muNumerator_eq_zipLookup]
    exact Nat.ne_of_gt hselected
  have hmem := zipLookup_ne_zero_index_mem _ _ _ hlookup
  have hstored := List.forall_iff_forall_mem.mp storedMuIndices_are_positiveSlots _ hmem
  exact ⟨(splitSlotIsValid_muFlatIndex_iff node region slot).mp hstored.1,
    splitShapeAt_muFlatIndex node region slot ▸ hstored.2⟩

/-- A nonzero stored `mu` numerator lies strictly below one half, directly from the sparse
chunk's checked open-interval invariant. -/
theorem selected_mu_bounds
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount)
    (hselected : 0 < muNumerator node region slot) :
    0 < muNumerator node region slot ∧
      muNumerator node region slot < halfDenominator := by
  have hlookup :
      zipLookup
        MatrixMultiplication.Generated.SimplifiedVolume.MuData0.data.scalarIndices.toList
        MatrixMultiplication.Generated.SimplifiedVolume.MuData0.data.numerators.toList
        (muFlatIndex node region slot) ≠ 0 := by
    rw [← muNumerator_eq_zipLookup]
    exact Nat.ne_of_gt hselected
  have hmem := zipLookup_ne_zero_value_mem _ _ _ hlookup
  rw [← muNumerator_eq_zipLookup] at hmem
  have hvalid := MatrixMultiplication.Generated.SimplifiedVolume.MuData0.data_isValid
  have hbound := MatrixMultiplication.Generated.SimplifiedVolume.All.of_mem hvalid.2.2.2 hmem
  exact ⟨hselected, by
    simpa [halfDenominator, localBits, AlgebraicComplexity.dyadicDenominator] using hbound.2⟩

/-- **Concrete selected-certificate leaf theorem.** Every level-two entry carrying a nonzero
stored `mu` in the simplified certificate instantiates the exact rational CW `112` leaf consumed
by both the retained-exponent and rectangular-volume evaluators. -/
theorem selectedLevelTwoEntry_instantiates_cw112
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount)
    (hselected : 0 < muNumerator node region slot) :
    InstantiatesCW112TypedLeaf node region slot := by
  have hbounds := selected_mu_bounds node region slot hselected
  exact instantiates_cw112_of_bounds node region slot
    (selected_mu_positiveSlot node region slot hselected) hbounds.1 hbounds.2

/-! ## Evaluator-input interface -/

/-- Interpret the stored heavy-coordinate number of a checked evaluator input as `Fin 3`. -/
def inputHeavy
    (input : Chunked.EdgeInput) (hheavy : input.heavyCoordinate < 3) : Fin 3 :=
  ⟨input.heavyCoordinate, hheavy⟩

/-- Semantic CW package for the minimal record consumed by all three retained-rate branches. -/
def InstantiatesCW112EdgeInput (input : Chunked.EdgeInput) : Prop :=
  ∃ (hheavy : input.heavyCoordinate < 3)
      (hmu : 0 < input.muNumerator) (hG : 0 < leafG input.muNumerator),
    cw112Mu input.muNumerator (leafG input.muNumerator) =
        mass localBits input.muNumerator ∧
      (∀ coordinate,
        Chunked.inputRate input coordinate =
          mass levelTwoOccurrenceBits input.occurrenceNumerator *
            orientedRetainedRateBits 5 input.muNumerator (leafG input.muNumerator)
              (by decide) hmu hG (inputHeavy input hheavy) coordinate) ∧
      mass levelTwoOccurrenceBits input.occurrenceNumerator *
          (∑ c, (cw112RationalTypedLeaf 5 input.muNumerator (leafG input.muNumerator)
            (by decide) hmu hG).dimensionRateBits c) =
        MatrixMultiplication.SimplifiedVolumeReconstruction.weightedPositiveEdgeValue
          levelTwoOccurrenceBits localBits input.occurrenceNumerator input.muNumerator

/-- Any evaluator input with a valid heavy coordinate and `mu ∈ (0,1/2)` is exactly the
corresponding rational CW `112` leaf.

Proof sketch: reuse the dyadic `mu`, entropy, and dimension identities above.  The only extra step
is identifying equality of `Fin 3` coordinates with equality of their stored natural values. -/
theorem edgeInput_instantiates_cw112_of_bounds
    (input : Chunked.EdgeInput)
    (hheavy : input.heavyCoordinate < 3)
    (hmu : 0 < input.muNumerator)
    (hhalf : input.muNumerator < halfDenominator) :
    InstantiatesCW112EdgeInput input := by
  let hG := leafG_pos hhalf
  refine ⟨hheavy, hmu, hG, cw112Mu_numerator_leafG_eq_mass hhalf, ?_,
    weighted_sum_dimensionRateBits_eq_evaluator _ _ hmu hhalf⟩
  intro coordinate
  rw [orientedRetainedRateBits_eq_evaluator _ hmu hhalf]
  unfold Chunked.inputRate
  by_cases hc : coordinate.val = input.heavyCoordinate
  · have heq : coordinate = inputHeavy input hheavy := Fin.ext hc
    simp [inputHeavy, heq]
  · have hne : coordinate ≠ inputHeavy input hheavy := by
      intro heq
      exact hc (congrArg Fin.val heq)
    simp [hc, hne]

end

end MatrixMultiplication.Generated.SimplifiedCW112Leaves
