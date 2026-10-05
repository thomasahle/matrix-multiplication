import MatrixMultiplication.Generated.TotalQuotientExponentStageFloors
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk2
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk5
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk6
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk8
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk9
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk10
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk11
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk13
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk14
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk15
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk16
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk17
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk18
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk19
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk20
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk21
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk22
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk23
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk24
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk25

/-! Regional level-four branch-2 floor certificate for region 1; certificate
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2

open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

def parentChunks : List (List ℕ) := [Chunk0.parents, Chunk1.parents, Chunk2.parents, Chunk3.parents, Chunk4.parents, Chunk5.parents, Chunk6.parents, Chunk7.parents, Chunk8.parents, Chunk9.parents, Chunk10.parents, Chunk11.parents, Chunk12.parents, Chunk13.parents, Chunk14.parents, Chunk15.parents, Chunk16.parents, Chunk17.parents, Chunk18.parents, Chunk19.parents, Chunk20.parents, Chunk21.parents, Chunk22.parents, Chunk23.parents, Chunk24.parents, Chunk25.parents]
def expectedParents : List ℕ := parentChunks.flatten
def expectedForms : List Form := [Chunk0.expectedForm, Chunk1.expectedForm, Chunk2.expectedForm, Chunk3.expectedForm, Chunk4.expectedForm, Chunk5.expectedForm, Chunk6.expectedForm, Chunk7.expectedForm, Chunk8.expectedForm, Chunk9.expectedForm, Chunk10.expectedForm, Chunk11.expectedForm, Chunk12.expectedForm, Chunk13.expectedForm, Chunk14.expectedForm, Chunk15.expectedForm, Chunk16.expectedForm, Chunk17.expectedForm, Chunk18.expectedForm, Chunk19.expectedForm, Chunk20.expectedForm, Chunk21.expectedForm, Chunk22.expectedForm, Chunk23.expectedForm, Chunk24.expectedForm, Chunk25.expectedForm]

noncomputable def expectedCertificates : List (LowerBound 116) :=
  [Chunk0.certificate, Chunk1.certificate, Chunk2.certificate, Chunk3.certificate, Chunk4.certificate, Chunk5.certificate, Chunk6.certificate, Chunk7.certificate, Chunk8.certificate, Chunk9.certificate, Chunk10.certificate, Chunk11.certificate, Chunk12.certificate, Chunk13.certificate, Chunk14.certificate, Chunk15.certificate, Chunk16.certificate, Chunk17.certificate, Chunk18.certificate, Chunk19.certificate, Chunk20.certificate, Chunk21.certificate, Chunk22.certificate, Chunk23.certificate, Chunk24.certificate, Chunk25.certificate]
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
    Chunk8.certificate_form,
    Chunk9.certificate_form,
    Chunk10.certificate_form,
    Chunk11.certificate_form,
    Chunk12.certificate_form,
    Chunk13.certificate_form,
    Chunk14.certificate_form,
    Chunk15.certificate_form,
    Chunk16.certificate_form,
    Chunk17.certificate_form,
    Chunk18.certificate_form,
    Chunk19.certificate_form,
    Chunk20.certificate_form,
    Chunk21.certificate_form,
    Chunk22.certificate_form,
    Chunk23.certificate_form,
    Chunk24.certificate_form,
    Chunk25.certificate_form]

/-- Exact reconstructed rate is the evaluation of the sum of bounded chunk forms. -/
theorem rate_eq :
    branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows Orientation.order
        Weights.Region1.dualWeights 1 expectedParents 2 =
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
    Chunk8.rate_eq,
    Chunk9.rate_eq,
    Chunk10.rate_eq,
    Chunk11.rate_eq,
    Chunk12.rate_eq,
    Chunk13.rate_eq,
    Chunk14.rate_eq,
    Chunk15.rate_eq,
    Chunk16.rate_eq,
    Chunk17.rate_eq,
    Chunk18.rate_eq,
    Chunk19.rate_eq,
    Chunk20.rate_eq,
    Chunk21.rate_eq,
    Chunk22.rate_eq,
    Chunk23.rate_eq,
    Chunk24.rate_eq,
    Chunk25.rate_eq]

/-- Directed regional endpoint obtained by adding the rational chunk endpoints. -/
noncomputable def lower : ℝ := 32380785299507612333416704461 / 18014398509481984000000000000

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
    Chunk8.certificate_lower,
    Chunk9.certificate_lower,
    Chunk10.certificate_lower,
    Chunk11.certificate_lower,
    Chunk12.certificate_lower,
    Chunk13.certificate_lower,
    Chunk14.certificate_lower,
    Chunk15.certificate_lower,
    Chunk16.certificate_lower,
    Chunk17.certificate_lower,
    Chunk18.certificate_lower,
    Chunk19.certificate_lower,
    Chunk20.certificate_lower,
    Chunk21.certificate_lower,
    Chunk22.certificate_lower,
    Chunk23.certificate_lower,
    Chunk24.certificate_lower,
    Chunk25.certificate_lower]
  norm_num [lower,
    Chunk0.lower,
    Chunk1.lower,
    Chunk2.lower,
    Chunk3.lower,
    Chunk4.lower,
    Chunk5.lower,
    Chunk6.lower,
    Chunk7.lower,
    Chunk8.lower,
    Chunk9.lower,
    Chunk10.lower,
    Chunk11.lower,
    Chunk12.lower,
    Chunk13.lower,
    Chunk14.lower,
    Chunk15.lower,
    Chunk16.lower,
    Chunk17.lower,
    Chunk18.lower,
    Chunk19.lower,
    Chunk20.lower,
    Chunk21.lower,
    Chunk22.lower,
    Chunk23.lower,
    Chunk24.lower,
    Chunk25.lower]

/-- The generated six-decimal regional floor is below the compact directed endpoint. -/
theorem floor_le_lower :
    MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.levelFourFloor
        ⟨1, by decide⟩ ≤ lower := by
  norm_num [MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.levelFourFloor,
    MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.levelFourFloorNumerators,
    MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.denominator, lower]

/-- The regional stage floor is below the exact reconstructed branch rate. -/
theorem floor_le_rate :
    MatrixMultiplication.Generated.TotalQuotientExponentStageFloors.levelFourFloor
        ⟨1, by decide⟩ ≤
      branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows Orientation.order
        Weights.Region1.dualWeights 1 expectedParents 2 := by
  calc
    _ ≤ lower := floor_le_lower
    _ = certificate.lower := lower_eq_certificate_lower
    _ ≤ Form.eval 116 certificate.form := certificate.lower_le_eval
    _ = Form.eval 116 (Form.sum expectedForms) :=
      congrArg (Form.eval 116) certificate_form
    _ = _ := rate_eq.symm

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2
