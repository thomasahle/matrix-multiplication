import AlgebraicComplexity.Analysis.ParentConsistencyGain
import AlgebraicComplexity.Probability.ParentConsistency
import AlgebraicComplexity.Probability.Rational
import MatrixMultiplication.LogBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Certificate interface for the active parent-consistency gain

The current level-4 point needs parent corrections only in two level-3 regional bottlenecks.
This file separates the exact, inexpensive active-branch arithmetic from reconstruction of the
large recursive certificate.

An `ActiveBranchTwoCertificate` records an old branch triple, a correction to branch two, and the
four inequalities proving that branch two is active before and after correction.  Its retained
gain is then exactly the correction.  Two such certificates, conservative local floors, and the
global reconstruction reserve prove the `17 / 10^6` gain consumed by the final decimal theorem.

Constructing the two records from the dyadic level-4 data remains a certificate-reconstruction
task.  The validity of the underlying correction is no longer assumed: it is supplied by
`CompatibilityPoolingModel.conditionalEntropyBits_le_sub_prescribedParentQuadratic`.
-/

namespace MatrixMultiplication.ParentGainCertificate

open AlgebraicComplexity
open AlgebraicComplexity.RegionalExponent

/-- Exact gain floor consumed by the final `2.369661` theorem. -/
noncomputable def certifiedGainFloor : ℝ := 17 / 1000000

/-- Conservative raw correction floor for level-3 region zero. -/
noncomputable def regionZeroRawFloor : ℝ := 93 / 10000000

/-- Conservative raw correction floor for level-3 region two. -/
noncomputable def regionTwoRawFloor : ℝ := 91 / 10000000

/-- Rational discrepancy sufficient for the region-zero raw floor when multiplied by the proved
`721 / 500` lower bound on `1 / log 2`. -/
def regionZeroDiscrepancyFloorRat : ℚ := 93 / 7210000

noncomputable def regionZeroDiscrepancyFloor : ℝ := regionZeroDiscrepancyFloorRat

/-- Rational discrepancy sufficient for the region-two raw floor. -/
def regionTwoDiscrepancyFloorRat : ℚ := 13 / 1030000

noncomputable def regionTwoDiscrepancyFloor : ℝ := regionTwoDiscrepancyFloorRat

/-- Aggregate reserve for reconstruction of the local laws and their outer weights. -/
noncomputable def reconstructionReserve : ℝ := 1 / (2 : ℝ) ^ 20

/-- Componentwise `L¹` radius used for each reconstructed local law and its weight. -/
noncomputable def localL1Reserve : ℝ := 1 / (2 : ℝ) ^ 24

/-- Lipschitz error bound for the weighted quadratic corrections. -/
noncomputable def analyticReconstructionError : ℝ :=
  6 * localL1Reserve / Real.log 2

/-- The exact analytic error estimate fits inside the simple power-of-two reserve. -/
theorem analyticReconstructionError_lt_reserve :
    analyticReconstructionError < reconstructionReserve := by
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [analyticReconstructionError]
  apply (div_lt_iff₀ hlogTwoPos).2
  have hlog := LogBounds.twoThirds_le_logTwo
  norm_num [localL1Reserve, reconstructionReserve] at hlog ⊢
  nlinarith

/-- A rational lower bound on a weighted max-normalized-square sum certifies a weighted
base-two quadratic correction.  This is the small exact-arithmetic interface expected from a
generated level-4 certificate. -/
theorem rawFloor_le_weightedQuadraticCorrection
    {Node Symbol : Type*} [Fintype Node] [Fintype Symbol]
    (weight : Node → ℝ)
    (parent decoupled : Node → ProbabilityVector Symbol)
    (hweight : ∀ node, 0 ≤ weight node)
    {rawFloor discrepancyFloor : ℝ}
    (harithmetic :
      rawFloor ≤ LogBounds.inverseLogTwoLower * (discrepancyFloor / 2))
    (hdiscrepancy :
      discrepancyFloor ≤
        ∑ node, weight node * (parent node).maxNormalizedSquare (decoupled node)) :
    rawFloor ≤
      ∑ node, weight node * (parent node).quadraticKlLowerBits (decoupled node) := by
  have hscale := mul_le_mul_of_nonneg_left hdiscrepancy
    (by norm_num [LogBounds.inverseLogTwoLower] : 0 ≤ LogBounds.inverseLogTwoLower / 2)
  have hrational :
      LogBounds.inverseLogTwoLower * (discrepancyFloor / 2) ≤
        ∑ node, weight node *
          (LogBounds.inverseLogTwoLower *
            ((parent node).maxNormalizedSquare (decoupled node) / 2)) := by
    calc
      LogBounds.inverseLogTwoLower * (discrepancyFloor / 2) =
          (LogBounds.inverseLogTwoLower / 2) * discrepancyFloor := by ring
      _ ≤ (LogBounds.inverseLogTwoLower / 2) *
          (∑ node, weight node *
            (parent node).maxNormalizedSquare (decoupled node)) := hscale
      _ = ∑ node, weight node *
          (LogBounds.inverseLogTwoLower *
            ((parent node).maxNormalizedSquare (decoupled node) / 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro node _
        ring
  exact harithmetic.trans <| hrational.trans <|
    ProbabilityVector.sum_weight_mul_inverseLogTwoLower_half_maxNormalizedSquare_le
      weight parent decoupled hweight LogBounds.inverseLogTwoLower_le_inv_logTwo

/-- Region-zero specialization of the rational discrepancy interface. -/
theorem regionZeroRawFloor_le_weightedQuadraticCorrection
    {Node Symbol : Type*} [Fintype Node] [Fintype Symbol]
    (weight : Node → ℝ)
    (parent decoupled : Node → ProbabilityVector Symbol)
    (hweight : ∀ node, 0 ≤ weight node)
    (hdiscrepancy :
      regionZeroDiscrepancyFloor ≤
        ∑ node, weight node * (parent node).maxNormalizedSquare (decoupled node)) :
    regionZeroRawFloor ≤
      ∑ node, weight node * (parent node).quadraticKlLowerBits (decoupled node) := by
  apply rawFloor_le_weightedQuadraticCorrection weight parent decoupled hweight
    (discrepancyFloor := regionZeroDiscrepancyFloor)
  · norm_num [regionZeroRawFloor, regionZeroDiscrepancyFloor,
      regionZeroDiscrepancyFloorRat, LogBounds.inverseLogTwoLower]
  · exact hdiscrepancy

/-- Region-two specialization of the rational discrepancy interface. -/
theorem regionTwoRawFloor_le_weightedQuadraticCorrection
    {Node Symbol : Type*} [Fintype Node] [Fintype Symbol]
    (weight : Node → ℝ)
    (parent decoupled : Node → ProbabilityVector Symbol)
    (hweight : ∀ node, 0 ≤ weight node)
    (hdiscrepancy :
      regionTwoDiscrepancyFloor ≤
        ∑ node, weight node * (parent node).maxNormalizedSquare (decoupled node)) :
    regionTwoRawFloor ≤
      ∑ node, weight node * (parent node).quadraticKlLowerBits (decoupled node) := by
  apply rawFloor_le_weightedQuadraticCorrection weight parent decoupled hweight
    (discrepancyFloor := regionTwoDiscrepancyFloor)
  · norm_num [regionTwoRawFloor, regionTwoDiscrepancyFloor,
      regionTwoDiscrepancyFloorRat, LogBounds.inverseLogTwoLower]
  · exact hdiscrepancy

/-- Convert an executable rational region-zero discrepancy certificate into the real quadratic
correction used by the entropy theorem. -/
theorem regionZeroRawFloor_le_of_rationalCertificate
    {Node Symbol : Type*} [Fintype Node] [Fintype Symbol]
    (weight : Node → ℚ)
    (parent decoupled : Node → RationalProbabilityData Symbol)
    (hweight : ∀ node, 0 ≤ weight node)
    (hparent : ∀ node, (parent node).IsProbability)
    (hdecoupled : ∀ node, (decoupled node).IsProbability)
    (hdiscrepancy :
      regionZeroDiscrepancyFloorRat ≤
        RationalProbabilityData.weightedMaxNormalizedSquare weight parent decoupled) :
    regionZeroRawFloor ≤
      ∑ node, (weight node : ℝ) *
        ((parent node).toReal (hparent node)).quadraticKlLowerBits
          ((decoupled node).toReal (hdecoupled node)) := by
  apply regionZeroRawFloor_le_weightedQuadraticCorrection
    (fun node ↦ (weight node : ℝ))
    (fun node ↦ (parent node).toReal (hparent node))
    (fun node ↦ (decoupled node).toReal (hdecoupled node))
  · intro node
    exact_mod_cast hweight node
  · rw [regionZeroDiscrepancyFloor,
      RationalProbabilityData.toReal_weightedMaxNormalizedSquare]
    exact_mod_cast hdiscrepancy

/-- Rational-data bridge for the region-two discrepancy certificate. -/
theorem regionTwoRawFloor_le_of_rationalCertificate
    {Node Symbol : Type*} [Fintype Node] [Fintype Symbol]
    (weight : Node → ℚ)
    (parent decoupled : Node → RationalProbabilityData Symbol)
    (hweight : ∀ node, 0 ≤ weight node)
    (hparent : ∀ node, (parent node).IsProbability)
    (hdecoupled : ∀ node, (decoupled node).IsProbability)
    (hdiscrepancy :
      regionTwoDiscrepancyFloorRat ≤
        RationalProbabilityData.weightedMaxNormalizedSquare weight parent decoupled) :
    regionTwoRawFloor ≤
      ∑ node, (weight node : ℝ) *
        ((parent node).toReal (hparent node)).quadraticKlLowerBits
          ((decoupled node).toReal (hdecoupled node)) := by
  apply regionTwoRawFloor_le_weightedQuadraticCorrection
    (fun node ↦ (weight node : ℝ))
    (fun node ↦ (parent node).toReal (hparent node))
    (fun node ↦ (decoupled node).toReal (hdecoupled node))
  · intro node
    exact_mod_cast hweight node
  · rw [regionTwoDiscrepancyFloor,
      RationalProbabilityData.toReal_weightedMaxNormalizedSquare]
    exact_mod_cast hdiscrepancy

/-- Transfer a raw rational discrepancy certificate to genuine real probability vectors once a
concrete reconstruction identifies every coordinate.  Unlike
`rawFloor_le_weightedQuadraticCorrection`'s earlier rational-data specialization, this theorem
does not ask the generated tables to prove their own simplex laws: validity belongs to the
semantic `ProbabilityVector`s, and the coordinate equalities are the explicit reconstruction
boundary. -/
theorem rawFloor_le_weightedQuadraticCorrection_of_rationalCoordinates
    {Node Symbol : Type*} [Fintype Node] [Fintype Symbol]
    (rationalWeight : Node → ℚ)
    (rationalParent rationalDecoupled : Node → RationalProbabilityData Symbol)
    (parent decoupled : Node → ProbabilityVector Symbol)
    (hweight : ∀ node, 0 ≤ rationalWeight node)
    (hparent : ∀ node symbol,
      (parent node).weight symbol = ((rationalParent node).weight symbol : ℝ))
    (hdecoupled : ∀ node symbol,
      (decoupled node).weight symbol = ((rationalDecoupled node).weight symbol : ℝ))
    {rawFloor : ℝ} {discrepancyFloor : ℚ}
    (harithmetic :
      rawFloor ≤ LogBounds.inverseLogTwoLower * ((discrepancyFloor : ℝ) / 2))
    (hdiscrepancy :
      discrepancyFloor ≤ RationalProbabilityData.weightedMaxNormalizedSquare
        rationalWeight rationalParent rationalDecoupled) :
    rawFloor ≤ ∑ node, (rationalWeight node : ℝ) *
      (parent node).quadraticKlLowerBits (decoupled node) := by
  apply rawFloor_le_weightedQuadraticCorrection
    (fun node ↦ (rationalWeight node : ℝ)) parent decoupled
  · intro node
    exact_mod_cast hweight node
  · exact harithmetic
  · have hcast :
        (discrepancyFloor : ℝ) ≤
          (RationalProbabilityData.weightedMaxNormalizedSquare
            rationalWeight rationalParent rationalDecoupled : ℝ) := by
      exact_mod_cast hdiscrepancy
    calc
      (discrepancyFloor : ℝ) ≤
          (RationalProbabilityData.weightedMaxNormalizedSquare
            rationalWeight rationalParent rationalDecoupled : ℝ) := hcast
      _ = ∑ node, (rationalWeight node : ℝ) *
          (parent node).maxNormalizedSquare (decoupled node) := by
        rw [← RationalProbabilityData.cast_weightedMaxNormalizedSquare]
        apply Finset.sum_congr rfl
        intro node _
        congr 1
        unfold ProbabilityVector.maxNormalizedSquare
        apply Finset.sum_congr rfl
        intro symbol _
        rw [hparent node symbol, hdecoupled node symbol]

/-- Region-zero raw-table transfer with an explicit coordinate reconstruction hypothesis. -/
theorem regionZeroRawFloor_le_of_rationalCoordinates
    {Node Symbol : Type*} [Fintype Node] [Fintype Symbol]
    (weight : Node → ℚ)
    (rationalParent rationalDecoupled : Node → RationalProbabilityData Symbol)
    (parent decoupled : Node → ProbabilityVector Symbol)
    (hweight : ∀ node, 0 ≤ weight node)
    (hparent : ∀ node symbol,
      (parent node).weight symbol = ((rationalParent node).weight symbol : ℝ))
    (hdecoupled : ∀ node symbol,
      (decoupled node).weight symbol = ((rationalDecoupled node).weight symbol : ℝ))
    (hdiscrepancy :
      regionZeroDiscrepancyFloorRat ≤
        RationalProbabilityData.weightedMaxNormalizedSquare
          weight rationalParent rationalDecoupled) :
    regionZeroRawFloor ≤ ∑ node, (weight node : ℝ) *
      (parent node).quadraticKlLowerBits (decoupled node) := by
  apply rawFloor_le_weightedQuadraticCorrection_of_rationalCoordinates
    weight rationalParent rationalDecoupled parent decoupled
    hweight hparent hdecoupled (discrepancyFloor := regionZeroDiscrepancyFloorRat)
  · norm_num [regionZeroRawFloor, regionZeroDiscrepancyFloorRat,
      LogBounds.inverseLogTwoLower]
  · exact hdiscrepancy

/-- Region-two counterpart of the coordinate reconstruction bridge. -/
theorem regionTwoRawFloor_le_of_rationalCoordinates
    {Node Symbol : Type*} [Fintype Node] [Fintype Symbol]
    (weight : Node → ℚ)
    (rationalParent rationalDecoupled : Node → RationalProbabilityData Symbol)
    (parent decoupled : Node → ProbabilityVector Symbol)
    (hweight : ∀ node, 0 ≤ weight node)
    (hparent : ∀ node symbol,
      (parent node).weight symbol = ((rationalParent node).weight symbol : ℝ))
    (hdecoupled : ∀ node symbol,
      (decoupled node).weight symbol = ((rationalDecoupled node).weight symbol : ℝ))
    (hdiscrepancy :
      regionTwoDiscrepancyFloorRat ≤
        RationalProbabilityData.weightedMaxNormalizedSquare
          weight rationalParent rationalDecoupled) :
    regionTwoRawFloor ≤ ∑ node, (weight node : ℝ) *
      (parent node).quadraticKlLowerBits (decoupled node) := by
  apply rawFloor_le_weightedQuadraticCorrection_of_rationalCoordinates
    weight rationalParent rationalDecoupled parent decoupled
    hweight hparent hdecoupled (discrepancyFloor := regionTwoDiscrepancyFloorRat)
  · norm_num [regionTwoRawFloor, regionTwoDiscrepancyFloorRat,
      LogBounds.inverseLogTwoLower]
  · exact hdiscrepancy

/-- A branch-two correction together with exact evidence that this branch remains the regional
bottleneck. -/
structure ActiveBranchTwoCertificate (floor : ℝ) where
  baseline : Fin 3 → ℝ
  correction : ℝ
  baseline_le_zero : baseline 2 ≤ baseline 0
  baseline_le_one : baseline 2 ≤ baseline 1
  corrected_le_zero : baseline 2 + correction ≤ baseline 0
  corrected_le_one : baseline 2 + correction ≤ baseline 1
  floor_le_correction : floor ≤ correction

/-- View the paper's branch-two record through the reusable arbitrary-active-branch interface. -/
noncomputable def ActiveBranchTwoCertificate.toGeneric {floor : ℝ}
    (C : ActiveBranchTwoCertificate floor) :
    RegionalExponent.ActiveBranchCertificate (2 : Fin 3) floor where
  baseline := C.baseline
  correction := fun branch ↦ if branch = 2 then C.correction else 0
  activeBefore := by
    intro branch
    fin_cases branch
    · exact C.baseline_le_zero
    · exact C.baseline_le_one
    · exact le_rfl
  activeAfter := by
    intro branch
    fin_cases branch
    · simpa [RegionalExponent.addCorrection] using C.corrected_le_zero
    · simpa [RegionalExponent.addCorrection] using C.corrected_le_one
    · exact le_rfl
  floor_le_correction := by
    simpa using C.floor_le_correction

/-- Retained-exponent gain represented by one active-branch certificate. -/
noncomputable def ActiveBranchTwoCertificate.retainedGain {floor : ℝ}
    (C : ActiveBranchTwoCertificate floor) : ℝ :=
  threeWayMin (correctBranchTwo C.baseline C.correction) - threeWayMin C.baseline

/-- The specialized and reusable active-branch interfaces compute the same retained gain. -/
theorem ActiveBranchTwoCertificate.toGeneric_retainedGain_eq {floor : ℝ}
    (C : ActiveBranchTwoCertificate floor) :
    C.toGeneric.retainedGain = C.retainedGain := by
  have hcorrect :
      RegionalExponent.addCorrection C.baseline C.toGeneric.correction =
        correctBranchTwo C.baseline C.correction := by
    funext branch
    fin_cases branch <;>
      simp [ActiveBranchTwoCertificate.toGeneric, RegionalExponent.addCorrection]
  unfold RegionalExponent.ActiveBranchCertificate.retainedGain
  unfold ActiveBranchTwoCertificate.retainedGain
  change threeWayMin
      (RegionalExponent.addCorrection C.baseline C.toGeneric.correction) -
        threeWayMin C.baseline =
    threeWayMin (correctBranchTwo C.baseline C.correction) - threeWayMin C.baseline
  rw [hcorrect]

theorem ActiveBranchTwoCertificate.retainedGain_eq {floor : ℝ}
    (C : ActiveBranchTwoCertificate floor) :
    C.retainedGain = C.correction := by
  rw [← C.toGeneric_retainedGain_eq, C.toGeneric.retainedGain_eq]
  simp [ActiveBranchTwoCertificate.toGeneric]

theorem ActiveBranchTwoCertificate.floor_le_retainedGain {floor : ℝ}
    (C : ActiveBranchTwoCertificate floor) :
    floor ≤ C.retainedGain := by
  rw [C.retainedGain_eq]
  exact C.floor_le_correction

/-- The two active level-3 regional corrections needed by the current certificate. -/
structure Data where
  regionZero : ActiveBranchTwoCertificate regionZeroRawFloor
  regionTwo : ActiveBranchTwoCertificate regionTwoRawFloor

/-- Corrected active gain after the single aggregate reconstruction reserve. -/
noncomputable def Data.certifiedGain (C : Data) : ℝ :=
  C.regionZero.retainedGain + C.regionTwo.retainedGain - reconstructionReserve

/-- Exact arithmetic showing why the two small local floors suffice. -/
theorem floor_add_floor_sub_reserve_ge :
    certifiedGainFloor ≤
      regionZeroRawFloor + regionTwoRawFloor - reconstructionReserve := by
  norm_num [certifiedGainFloor, regionZeroRawFloor, regionTwoRawFloor,
    reconstructionReserve]

/-- Every valid two-region certificate establishes the directed gain used by the headline
decimal. -/
theorem certifiedGainFloor_le (C : Data) :
    certifiedGainFloor ≤ C.certifiedGain := by
  have hzero := C.regionZero.floor_le_retainedGain
  have htwo := C.regionTwo.floor_le_retainedGain
  exact floor_add_floor_sub_reserve_ge.trans (by
    unfold Data.certifiedGain
    linarith)

theorem certifiedGainFloor_pos : 0 < certifiedGainFloor := by
  norm_num [certifiedGainFloor]

end MatrixMultiplication.ParentGainCertificate
