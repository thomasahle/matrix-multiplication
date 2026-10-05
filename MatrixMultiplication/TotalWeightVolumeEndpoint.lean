import AlgebraicComplexity.Examples.CoppersmithWinogradVolumeEndpoint
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume
import MatrixMultiplication.CurrentProofObligations
import MatrixMultiplication.Generated.TotalQuotientExponentScalarData
import MatrixMultiplication.Generated.TotalQuotientVolumeScalarData

set_option autoImplicit false

/-!
# Exact endpoint for the total-weight quotient certificate

The generated scalar checkers expose two conservative real witnesses: the retained-copy
exponent and the sum of the three logarithmic matrix dimensions.  This file is the deliberately
narrow endpoint adapter.  It asks a semantic reconstruction theorem to place those two witnesses
below the exponents of an actual extraction sequence and performs all remaining arithmetic in
Lean.

No entropy formula, certificate array, or tensor-extraction assertion is hidden in the endpoint.
In particular, `Reconstruction` is still a genuine hypothesis until the generated recurrence is
identified with the finite total-weight construction.
-/

namespace MatrixMultiplication.TotalWeightVolumeEndpoint

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.CurrentProofObligations

universe u

/-- Directed retained-exponent floor from the e798 total-weight certificate. -/
noncomputable abbrev retainedFloor : ℝ :=
  MatrixMultiplication.Generated.TotalQuotientExponentScalar.retainedExponentFloor

/-- Directed mean rectangular-volume floor from the same certificate. -/
noncomputable abbrev volumeFloor : ℝ :=
  MatrixMultiplication.Generated.TotalQuotientVolumeScalar.volumeFloor

/-- Exact rational endpoint represented by the decimal `2.36588731`. -/
noncomputable def omegaTarget : ℝ := 236588731 / 100000000

/-- The requested formalization milestone. -/
noncomputable def acceptanceTarget : ℝ := 236999 / 100000

/-- A deliberately coarse retained-exponent floor sufficient for the requested endpoint.

The tight generated witness is needed for `2.36588731`, but not for `2.36999`.  Exposing this
separate floor lets the semantic construction close the requested theorem without first proving
every last decimal of the stronger numerical reconstruction. -/
noncomputable def acceptanceRetainedFloor : ℝ := 411 / 50

/-- Conservative split of the requested retained floor assigned to the quotient/hash stages. -/
noncomputable def acceptanceOuterRetainedFloor : ℝ := 16193 / 2500

/-- Conservative split assigned to the canonical level-two inner extraction. -/
noncomputable def acceptanceInnerRetainedFloor : ℝ := 4357 / 2500

theorem volumeFloor_pos : 0 < volumeFloor := by
  norm_num [volumeFloor,
    MatrixMultiplication.Generated.TotalQuotientVolumeScalar.volumeFloor]

theorem omegaTarget_nonneg : 0 ≤ omegaTarget := by
  norm_num [omegaTarget]

theorem omegaTarget_lt_acceptanceTarget : omegaTarget < acceptanceTarget := by
  norm_num [omegaTarget, acceptanceTarget]

theorem acceptanceTarget_nonneg : 0 ≤ acceptanceTarget := by
  norm_num [acceptanceTarget]

theorem acceptanceRetainedFloor_pos : 0 < acceptanceRetainedFloor := by
  norm_num [acceptanceRetainedFloor]

theorem acceptanceRetainedFloor_eq_outer_add_inner :
    acceptanceRetainedFloor =
      acceptanceOuterRetainedFloor + acceptanceInnerRetainedFloor := by
  norm_num [acceptanceRetainedFloor, acceptanceOuterRetainedFloor,
    acceptanceInnerRetainedFloor]

/-- The generated coordinate-sum witness strictly clears three times the directed mean-volume
floor. -/
theorem volumeFloor_lt_generatedMean :
    volumeFloor <
      MatrixMultiplication.Generated.TotalQuotientVolumeScalar.scalarCoordinateSum / 3 := by
  have h :=
    MatrixMultiplication.Generated.TotalQuotientVolumeScalar.three_mul_volumeFloor_lt_scalarCoordinateSum
  change (3 : ℝ) * volumeFloor <
      MatrixMultiplication.Generated.TotalQuotientVolumeScalar.scalarCoordinateSum at h
  linarith

/-- Exact positive endpoint margin.  Against the directed source-rank upper enclosure it is
`4523713 / 125000000000000`. -/
theorem certified_endpoint_slack :
    MatrixMultiplication.LogBounds.rankBudgetUpper <
      retainedFloor + omegaTarget * volumeFloor := by
  norm_num [MatrixMultiplication.LogBounds.rankBudgetUpper, retainedFloor,
    MatrixMultiplication.Generated.TotalQuotientExponentScalar.retainedExponentFloor,
    omegaTarget, volumeFloor,
    MatrixMultiplication.Generated.TotalQuotientVolumeScalar.volumeFloor]

/-- The coarse total-weight acceptance floor `8.22` is a separate endpoint interface (it is not
the simplified-volume floor `8.2` and is not used for the tight `2.36588731` target).  It has
substantially more arithmetic reserve than the tight candidate: the exact margin against the
directed source-rank enclosure is
`66830512879 / 25000000000000 > 0`. -/
theorem certified_acceptance_slack :
    MatrixMultiplication.LogBounds.rankBudgetUpper <
      acceptanceRetainedFloor + acceptanceTarget * volumeFloor := by
  norm_num [MatrixMultiplication.LogBounds.rankBudgetUpper, acceptanceRetainedFloor,
    acceptanceTarget, volumeFloor,
    MatrixMultiplication.Generated.TotalQuotientVolumeScalar.volumeFloor]

/-- Semantic boundary between the generated scalar expressions and an actual extraction
sequence.  The second witness is divided by three because cyclic rectangular symmetrization uses
the arithmetic mean of the three logarithmic dimensions. -/
def Reconstruction (retained volume : ℝ) : Prop :=
  MatrixMultiplication.Generated.TotalQuotientExponentScalar.retainedExponentLowerWitness ≤
      retained ∧
    MatrixMultiplication.Generated.TotalQuotientVolumeScalar.scalarCoordinateSum / 3 ≤ volume

/-- Coarser semantic boundary sufficient for the requested `2.36999` theorem.

Unlike `Reconstruction`, this interface does not require identifying the semantic retained rate
with the tightly compressed aggregate scalar witness.  It asks only for the two rational floors
actually needed by the requested endpoint. -/
def AcceptanceReconstruction (retained volume : ℝ) : Prop :=
  acceptanceRetainedFloor ≤ retained ∧ volumeFloor ≤ volume

/-- Assemble the deliberately slack outer/inner floors into the coarse endpoint interface. -/
theorem acceptanceReconstruction_addRetained
    {outerRetained innerRetained volume : ℝ}
    (houter : acceptanceOuterRetainedFloor ≤ outerRetained)
    (hinner : acceptanceInnerRetainedFloor ≤ innerRetained)
    (hvolume : volumeFloor ≤ volume) :
    AcceptanceReconstruction (outerRetained + innerRetained) volume := by
  constructor
  · rw [acceptanceRetainedFloor_eq_outer_add_inner]
    exact add_le_add houter hinner
  · exact hvolume

/-- A total-weight extraction sequence satisfying the two generated semantic inequalities proves
the advertised exact endpoint. -/
theorem omega_lt_236588731_of_subexponentialVolumeSequence
    (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hreconstruct : Reconstruction retained volume) :
    omega K < omegaTarget := by
  rcases hreconstruct with ⟨hretainedWitness, hvolumeWitness⟩
  have hretained : retainedFloor ≤ retained :=
    (le_of_lt
      MatrixMultiplication.Generated.TotalQuotientExponentScalar.retainedExponentFloor_lt_retainedExponentLowerWitness).trans
        hretainedWitness
  have hvolume : volumeFloor ≤ volume :=
    (le_of_lt volumeFloor_lt_generatedMean).trans hvolumeWitness
  apply omega_lt_of_cwPower_volumeSequence_lowerBounds K 5 8
    volumeFloor_pos hretained hvolume omegaTarget_nonneg hextractions
  calc
    (8 : ℝ) * Real.log ((5 : ℕ) + 2) / Real.log 2 = sourceRankBudget := by
      norm_num [sourceRankBudget]
      ring
    _ < MatrixMultiplication.LogBounds.rankBudgetUpper := sourceRankBudget_lt_upper
    _ < retainedFloor + omegaTarget * volumeFloor := certified_endpoint_slack

/-- Whole-constituent sequence form of the exact total-weight endpoint. -/
theorem omega_lt_236588731_of_wholeConstituentSequenceData
    (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (data : WholeConstituentLaserVolumeSequenceData K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hreconstruct : Reconstruction retained volume) :
    omega K < omegaTarget :=
  omega_lt_236588731_of_subexponentialVolumeSequence K
    data.toSubexponentialLaserVolumeSequence hreconstruct

/-- Requested milestone, as an immediate weakening of the stronger total-weight endpoint. -/
theorem omega_lt_236999_of_subexponentialVolumeSequence
    (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hreconstruct : Reconstruction retained volume) :
    omega K < acceptanceTarget :=
  (omega_lt_236588731_of_subexponentialVolumeSequence
    K hextractions hreconstruct).trans omegaTarget_lt_acceptanceTarget

/-- Requested milestone from the no-hole whole-constituent sequence interface. -/
theorem omega_lt_236999_of_wholeConstituentSequenceData
    (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (data : WholeConstituentLaserVolumeSequenceData K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hreconstruct : Reconstruction retained volume) :
    omega K < acceptanceTarget :=
  omega_lt_236999_of_subexponentialVolumeSequence K
    data.toSubexponentialLaserVolumeSequence hreconstruct

/-- Direct requested endpoint from the coarse semantic floors.  This is the shortest final
consumer for the concrete total-weight sequence. -/
theorem omega_lt_236999_of_subexponentialVolumeSequence_acceptanceFloors
    (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hreconstruct : AcceptanceReconstruction retained volume) :
    omega K < acceptanceTarget := by
  rcases hreconstruct with ⟨hretained, hvolume⟩
  apply omega_lt_of_cwPower_volumeSequence_lowerBounds K 5 8
    volumeFloor_pos hretained hvolume acceptanceTarget_nonneg
    hextractions
  calc
    (8 : ℝ) * Real.log ((5 : ℕ) + 2) / Real.log 2 = sourceRankBudget := by
      norm_num [sourceRankBudget]
      ring
    _ < MatrixMultiplication.LogBounds.rankBudgetUpper := sourceRankBudget_lt_upper
    _ < acceptanceRetainedFloor + acceptanceTarget * volumeFloor :=
      certified_acceptance_slack

/-- Whole-constituent form of the coarse requested endpoint. -/
theorem omega_lt_236999_of_wholeConstituentSequenceData_acceptanceFloors
    (K : Type u) [Field K]
    {stride : ℕ} {retained volume : ℝ}
    (data : WholeConstituentLaserVolumeSequenceData K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hreconstruct : AcceptanceReconstruction retained volume) :
    omega K < acceptanceTarget :=
  omega_lt_236999_of_subexponentialVolumeSequence_acceptanceFloors K
    data.toSubexponentialLaserVolumeSequence hreconstruct

/-- Requested endpoint in the exact outer-plus-inner normalization returned by nested
total-weight composition. -/
theorem omega_lt_236999_of_subexponentialVolumeSequence_outer_inner_floors
    (K : Type u) [Field K]
    {stride : ℕ} {outerRetained innerRetained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * (outerRetained + innerRetained)))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (houter : acceptanceOuterRetainedFloor ≤ outerRetained)
    (hinner : acceptanceInnerRetainedFloor ≤ innerRetained)
    (hvolume : volumeFloor ≤ volume) :
    omega K < acceptanceTarget :=
  omega_lt_236999_of_subexponentialVolumeSequence_acceptanceFloors K hextractions
    (acceptanceReconstruction_addRetained houter hinner hvolume)

theorem omegaTarget_eq_decimal : omegaTarget = 2.36588731 := by
  norm_num [omegaTarget]

theorem acceptanceTarget_eq_decimal : acceptanceTarget = 2.36999 := by
  norm_num [acceptanceTarget]

end MatrixMultiplication.TotalWeightVolumeEndpoint
