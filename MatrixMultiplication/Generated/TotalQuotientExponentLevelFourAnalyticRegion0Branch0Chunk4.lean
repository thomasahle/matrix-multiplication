import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch0Chunk4Parent0Certificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch0Chunk4Parent1Certificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch0Chunk4Parent2Certificate
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch0Chunk4Parent3Certificate

/-! Compact exact branch checker for level-four region 0, branch 0, parent chunk
4; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.  Only a canonical signed-log sufficient statistic is
stored.  Logical-`X` reconstruction is delegated to one isolated root-projection module per
parent, so unrelated dense compatibility rows never enter this aggregate environment. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch0.Chunk4

open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

def parents : List ℕ := [52, 53, 54, 55]
def parentChunks : List (List ℕ) := [[Parent0.parent], [Parent1.parent], [Parent2.parent], [Parent3.parent]]
def expectedForms : List Form := [Parent0.expectedForm, Parent1.expectedForm, Parent2.expectedForm, Parent3.expectedForm]
def expectedForm : Form := Form.sum expectedForms

noncomputable def expectedCertificates : List (LowerBound 116) :=
  [Parent0.certificate, Parent1.certificate, Parent2.certificate, Parent3.certificate]

/-- Lower certificate for the chunk, assembled only from independently sealed parent checks. -/
noncomputable def certificate : LowerBound 116 :=
  LowerBound.sum expectedCertificates

theorem certificate_form : certificate.form = expectedForm := by
  rw [certificate, LowerBound.sum_form]
  simp [expectedCertificates, expectedForms, expectedForm]

/-- Exact reconstructed rate is the sum of the independently checked parent forms. -/
theorem rate_eq :
    branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows Orientation.order
        Weights.Region0.dualWeights 0 parents 0 =
      Form.eval 116 expectedForm := by
  rw [show parents = parentChunks.flatten by decide]
  rw [branchRateOnParentsFrom_flatten]
  unfold expectedForm
  rw [Form.eval_sum]
  unfold parentChunks expectedForms
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [Parent0.rate_eq,
    Parent1.rate_eq,
    Parent2.rate_eq,
    Parent3.rate_eq]

/-- Directed chunk endpoint obtained by adding the parent endpoints. -/
noncomputable def lower : ℝ := 10108233003 / 64000000000000

theorem lower_eq_certificate_lower : lower = certificate.lower := by
  rw [certificate, LowerBound.sum_lower]
  simp only [expectedCertificates, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Parent0.certificate_lower, Parent1.certificate_lower, Parent2.certificate_lower, Parent3.certificate_lower]
  norm_num [lower,
    Parent0.lower,
    Parent1.lower,
    Parent2.lower,
    Parent3.lower]

/-- The directed rational chunk endpoint is below the exact reconstructed branch rate. -/
theorem lower_le_rate :
    lower ≤ branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows
      Orientation.order Weights.Region0.dualWeights 0 parents 0 := by
  calc
    _ = certificate.lower := lower_eq_certificate_lower
    _ ≤ Form.eval 116 certificate.form := certificate.lower_le_eval
    _ = Form.eval 116 expectedForm :=
      congrArg (Form.eval 116) certificate_form
    _ = _ := rate_eq.symm

@[simp] theorem certificate_lower : certificate.lower = lower :=
  lower_eq_certificate_lower.symm

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch0.Chunk4
