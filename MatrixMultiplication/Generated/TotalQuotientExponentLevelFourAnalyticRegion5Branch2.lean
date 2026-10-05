import MatrixMultiplication.Generated.TotalQuotientExponentStageFloors
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion5
import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk4
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk5
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk6
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk7
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk8

/-! Regional level-four branch-2 floor certificate for region 5; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2

open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

def parentChunks : List (List ℕ) := [Chunk0.parents, Chunk1.parents, Chunk2.parents, Chunk3.parents, Chunk4.parents, Chunk5.parents, Chunk6.parents, Chunk7.parents, Chunk8.parents]
def expectedParents : List ℕ := parentChunks.flatten
def expectedForms : List Form := [Chunk0.expectedForm, Chunk1.expectedForm, Chunk2.expectedForm, Chunk3.expectedForm, Chunk4.expectedForm, Chunk5.expectedForm, Chunk6.expectedForm, Chunk7.expectedForm, Chunk8.expectedForm]

noncomputable def expectedCertificates : List (LowerBound 116) :=
  [Chunk0.certificate, Chunk1.certificate, Chunk2.certificate, Chunk3.certificate, Chunk4.certificate, Chunk5.certificate, Chunk6.certificate, Chunk7.certificate, Chunk8.certificate]
noncomputable def certificate : LowerBound 116 :=
  LowerBound.sum expectedCertificates

theorem certificate_form : certificate.form = Form.sum expectedForms := by
  rw [certificate, LowerBound.sum_form]
  simp only [expectedCertificates, expectedForms, List.map_cons, List.map_nil,
    Chunk0.certificate_form,
    Chunk1.certificate_form,
    Chunk2.certificate_form,
    Chunk3.certificate_form,
    Chunk4.certificate_form,
    Chunk5.certificate_form,
    Chunk6.certificate_form,
    Chunk7.certificate_form,
    Chunk8.certificate_form]

/-- Exact reconstructed rate is the evaluation of the sum of bounded chunk forms. -/
theorem rate_eq :
    branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows Orientation.order
        Weights.Region5.dualWeights 5 expectedParents 2 =
      Form.eval 116 (Form.sum expectedForms) := by
  unfold expectedParents
  rw [branchRateOnParentsFrom_flatten, Form.eval_sum]
  unfold parentChunks expectedForms
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [Chunk0.rate_eq,
    Chunk1.rate_eq,
    Chunk2.rate_eq,
    Chunk3.rate_eq,
    Chunk4.rate_eq,
    Chunk5.rate_eq,
    Chunk6.rate_eq,
    Chunk7.rate_eq,
    Chunk8.rate_eq]

/-- Directed regional endpoint obtained by adding the rational chunk endpoints. -/
noncomputable def lower : ℝ := 14625575088517670543833523 / 36028797018963968000000000000

theorem lower_eq_certificate_lower : lower = certificate.lower := by
  rw [certificate, LowerBound.sum_lower]
  simp only [expectedCertificates, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Chunk0.certificate_lower,
    Chunk1.certificate_lower,
    Chunk2.certificate_lower,
    Chunk3.certificate_lower,
    Chunk4.certificate_lower,
    Chunk5.certificate_lower,
    Chunk6.certificate_lower,
    Chunk7.certificate_lower,
    Chunk8.certificate_lower]
  norm_num [lower,
    Chunk0.lower,
    Chunk1.lower,
    Chunk2.lower,
    Chunk3.lower,
    Chunk4.lower,
    Chunk5.lower,
    Chunk6.lower,
    Chunk7.lower,
    Chunk8.lower]

/-- The generated six-decimal regional floor is below the compact directed endpoint. -/
theorem floor_le_lower :
    MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.levelFourFloor
        ⟨5, by decide⟩ ≤ lower := by
  norm_num [MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.levelFourFloor,
    MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.levelFourFloorNumerators,
    MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.denominator, lower]

/-- The regional stage floor is below the exact reconstructed branch rate. -/
theorem floor_le_rate :
    MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.levelFourFloor
        ⟨5, by decide⟩ ≤
      branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows Orientation.order
        Weights.Region5.dualWeights 5 expectedParents 2 := by
  calc
    _ ≤ lower := floor_le_lower
    _ = certificate.lower := lower_eq_certificate_lower
    _ ≤ Form.eval 116 certificate.form := certificate.lower_le_eval
    _ = Form.eval 116 (Form.sum expectedForms) :=
      congrArg (Form.eval 116) certificate_form
    _ = _ := rate_eq.symm

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2
