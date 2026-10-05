import MatrixMultiplication.Generated.TotalQuotientExponentStageFloors
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion3
import MatrixMultiplication.SignedDyadicLogCertificate


/-! Regional level-four branch-1 floor certificate for region 3; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region3.Branch1

open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

def parentChunks : List (List ℕ) := []
def expectedParents : List ℕ := parentChunks.flatten
def expectedForms : List Form := []

noncomputable def expectedCertificates : List (LowerBound 116) :=
  []
noncomputable def certificate : LowerBound 116 :=
  LowerBound.sum expectedCertificates

theorem certificate_form : certificate.form = Form.sum expectedForms := by
  rw [certificate, LowerBound.sum_form]
  simp only [expectedCertificates, expectedForms, List.map_nil]

/-- Exact reconstructed rate is the evaluation of the sum of bounded chunk forms. -/
theorem rate_eq :
    branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows Orientation.order
        Weights.Region3.dualWeights 3 expectedParents 1 =
      Form.eval 116 (Form.sum expectedForms) := by
  unfold expectedParents
  rw [branchRateOnParentsFrom_flatten, Form.eval_sum]
  unfold parentChunks expectedForms
  simp only [List.map_nil, List.sum_nil]


/-- Directed regional endpoint obtained by adding the rational chunk endpoints. -/
noncomputable def lower : ℝ := 0 / 1

theorem lower_eq_certificate_lower : lower = certificate.lower := by
  rw [certificate, LowerBound.sum_lower]
  simp only [expectedCertificates, List.map_nil, List.sum_nil]
  norm_num [lower]

/-- The generated six-decimal regional floor is below the compact directed endpoint. -/
theorem floor_le_lower :
    MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.levelFourFloor
        ⟨3, by decide⟩ ≤ lower := by
  norm_num [MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.levelFourFloor,
    MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.levelFourFloorNumerators,
    MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.denominator, lower]

/-- The regional stage floor is below the exact reconstructed branch rate. -/
theorem floor_le_rate :
    MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.levelFourFloor
        ⟨3, by decide⟩ ≤
      branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows Orientation.order
        Weights.Region3.dualWeights 3 expectedParents 1 := by
  calc
    _ ≤ lower := floor_le_lower
    _ = certificate.lower := lower_eq_certificate_lower
    _ ≤ Form.eval 116 certificate.form := certificate.lower_le_eval
    _ = Form.eval 116 (Form.sum expectedForms) :=
      congrArg (Form.eval 116) certificate_form
    _ = _ := rate_eq.symm

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region3.Branch1
