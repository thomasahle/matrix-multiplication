import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Data.List.SplitLengths
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch0Chunk22TermsParent0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch0Chunk22Parent0

/-! Independently sealed numeric certificate for level-four region 1, branch 0,
parent chunk 22, parent 90; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk22

open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

noncomputable def shardCertificates : List (LowerBound 116) :=
  [TermShard0.certificate]

/-- Compositional lower certificate assembled from the small numeric term shards. -/
noncomputable def expectedCertificate : LowerBound 116 :=
  LowerBound.add (LowerBound.constant 116 64491724286611170801144775573504)
    (LowerBound.sum shardCertificates)

/-- The bounded shard certificates reconstruct this parent's complete exact form. -/
theorem expectedCertificate_form : expectedCertificate.form = expectedForm := by
  unfold expectedCertificate
  change Form.add (LowerBound.constant 116 64491724286611170801144775573504).form
      (LowerBound.sum shardCertificates).form = expectedForm
  rw [LowerBound.sum_form]
  simp only [shardCertificates]
  rfl

/-- Directed rational endpoint after summing this parent's term-shard endpoints. -/
noncomputable def lower : ℝ := 40369841863 / 128000000000000

/-- The serialized rational endpoint is exactly the compositional certificate endpoint. -/
theorem lower_eq_expectedCertificate_lower : lower = expectedCertificate.lower := by
  norm_num [lower, expectedCertificate, shardCertificates,
    LowerBound.add, LowerBound.constant,
    LowerBound.sum, LowerBound.ofSignedFamilies,
    TermShard0.lower, TermShard0.positiveFloor, TermShard0.negativeCeiling, TermShard0.constantNumerator, TermShard0.bits]

/-- The directed endpoint is below the exact reconstructed parent form. -/
theorem lower_le_expectedForm_eval :
    lower ≤ Form.eval 116 expectedForm := by
  rw [lower_eq_expectedCertificate_lower, ← expectedCertificate_form]
  exact expectedCertificate.lower_le_eval

/-- Exact branch value contributed by this parent. -/
theorem rate_eq :
    branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows
        Orientation.order Weights.Region1.dualWeights 1 [parent] 0 =
      Form.eval 116 expectedForm := by
  have heval := congrArg (Form.eval 116) recurrence_structuralPowerCanonical
  rw [Form.eval_structuralPowerCanonical, branchFormOnParentsFrom_eval] at heval
  exact heval

/-- This parent's directed endpoint is below its reconstructed branch rate. -/
theorem lower_le_rate :
    lower ≤ branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows
      Orientation.order Weights.Region1.dualWeights 1 [parent] 0 := by
  rw [rate_eq]
  exact lower_le_expectedForm_eval

/-- The parent endpoint and exact form, packaged for chunk composition. -/
noncomputable def certificate : LowerBound 116 :=
  { form := expectedForm
    lower := lower
    lower_le_eval := lower_le_expectedForm_eval }

@[simp] theorem certificate_form : certificate.form = expectedForm := rfl
@[simp] theorem certificate_lower : certificate.lower = lower := rfl

end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk22
