import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Data.List.SplitLengths
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10TermsParent0
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10Parent0

/-! Independently sealed numeric certificate for level-four region 1, branch 1,
parent chunk 10, parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10

open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

/-- Constant-only raw form preceding the source-order logarithmic shards. -/
def rawBaseForm : Form := { constantNumerator := 0, terms := [] }

/-- Source-order raw logarithmic forms before independent power extraction. -/
def rawForms : List Form := [rawBaseForm, TermShard0.rawForm, TermShard1.rawForm, TermShard2.rawForm, TermShard3.rawForm, TermShard4.rawForm]

/-- All certificate shards, including the exact source constant. -/
noncomputable def expectedCertificates : List (LowerBound 116) :=
  [LowerBound.constant 116 0, TermShard0.certificate, TermShard1.certificate, TermShard2.certificate, TermShard3.certificate, TermShard4.certificate]

/-- Compositional lower certificate assembled from the bounded numeric shards. -/
noncomputable def expectedCertificate : LowerBound 116 :=
  LowerBound.sum expectedCertificates

/-- Raw shard term lists in their original source order. -/
def rawTermChunks : List (List Term) := [TermShard0.rawForm.terms, TermShard1.rawForm.terms, TermShard2.rawForm.terms, TermShard3.rawForm.terms, TermShard4.rawForm.terms]

/-- Bounded chunk sizes used to recover the complete source term list. -/
def termChunkSizes : List ℕ := [64, 64, 64, 64, 9]

/-- The corresponding bounded slices of the semantic raw form. -/
def expectedRawTermChunks : List (List Term) :=
  termChunkSizes.splitLengths expectedRaw.terms

/-- Bounded source slice represented by raw shard 0. -/
theorem rawTermChunk0_eq :
    TermShard0.rawForm.terms = (expectedRaw.terms).take 64 := by
  rfl
/-- Bounded source slice represented by raw shard 1. -/
theorem rawTermChunk1_eq :
    TermShard1.rawForm.terms = ((expectedRaw.terms).drop 64).take 64 := by
  rfl
/-- Bounded source slice represented by raw shard 2. -/
theorem rawTermChunk2_eq :
    TermShard2.rawForm.terms = (((expectedRaw.terms).drop 64).drop 64).take 64 := by
  rfl
/-- Bounded source slice represented by raw shard 3. -/
theorem rawTermChunk3_eq :
    TermShard3.rawForm.terms = ((((expectedRaw.terms).drop 64).drop 64).drop 64).take 64 := by
  rfl
/-- Bounded source slice represented by raw shard 4. -/
theorem rawTermChunk4_eq :
    TermShard4.rawForm.terms = (((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).take 9 := by
  rfl

/-- The semantic raw form has the serialized source constant. -/
theorem expectedRaw_constant : expectedRaw.constantNumerator = 0 := by
  rfl

/-- The semantic raw form has exactly the serialized number of logarithmic terms. -/
theorem expectedRaw_terms_length : expectedRaw.terms.length = 265 := by
  rfl

/-- The independently checked raw shards are exactly the bounded semantic source slices. -/
theorem rawTermChunks_eq_expectedRawTermChunks :
    rawTermChunks = expectedRawTermChunks := by
  unfold rawTermChunks expectedRawTermChunks termChunkSizes
  simp only [List.splitLengths_cons, List.splitLengths_nil]
  rw [rawTermChunk0_eq, rawTermChunk1_eq, rawTermChunk2_eq, rawTermChunk3_eq, rawTermChunk4_eq]

/-- The bounded source slices cover the complete semantic raw term list. -/
theorem expectedRawTermChunks_flatten :
    expectedRawTermChunks.flatten = expectedRaw.terms := by
  unfold expectedRawTermChunks
  apply List.flatten_splitLengths
  rw [expectedRaw_terms_length]
  norm_num [termChunkSizes]

/-- Projecting terms from the raw form list gives precisely the explicit raw chunks. -/
theorem rawForms_terms :
    (rawForms.map fun form ↦ form.terms).flatten = rawTermChunks.flatten := by
  unfold rawForms rawBaseForm rawTermChunks
  rfl

/-- The raw forms' constants sum to the semantic source constant. -/
theorem rawForms_constant :
    (rawForms.map fun form ↦ form.constantNumerator).sum =
      expectedRaw.constantNumerator := by
  rw [expectedRaw_constant]
  norm_num [rawForms, rawBaseForm, TermShard0.rawForm_constant, TermShard1.rawForm_constant, TermShard2.rawForm_constant, TermShard3.rawForm_constant, TermShard4.rawForm_constant]

/-- Ordinary list laws reassemble the bounded raw shards into the semantic source form. -/
theorem rawForms_sum_eq_expectedRaw : Form.sum rawForms = expectedRaw := by
  apply Form.ext
  · rw [Form.sum_constantNumerator, rawForms_constant]
  · rw [Form.sum_terms, rawForms_terms,
      rawTermChunks_eq_expectedRawTermChunks, expectedRawTermChunks_flatten]

/-- Every independently normalized certificate shard preserves the evaluation of its raw slice. -/
theorem expectedCertificates_eval_rawForms : List.Forall₂
    (fun certificate form ↦
      Form.eval 116 certificate.form = Form.eval 116 form)
    expectedCertificates rawForms := by
  unfold expectedCertificates rawForms rawBaseForm
  constructor
  · rfl
  constructor
  · exact TermShard0.form_eval_rawForm
  constructor
  · exact TermShard1.form_eval_rawForm
  constructor
  · exact TermShard2.form_eval_rawForm
  constructor
  · exact TermShard3.form_eval_rawForm
  constructor
  · exact TermShard4.form_eval_rawForm
  constructor

/-- Directed rational endpoint after summing this parent's term-shard endpoints. -/
noncomputable def lower : ℝ := 145790342445334702526121699 / 4503599627370496000000000000

/-- The serialized rational endpoint is exactly the compositional certificate endpoint. -/
theorem lower_eq_expectedCertificate_lower : lower = expectedCertificate.lower := by
  rw [expectedCertificate, LowerBound.sum_lower]
  change lower = (LowerBound.constant 116 0).lower + (TermShard0.certificate.lower + (TermShard1.certificate.lower + (TermShard2.certificate.lower + (TermShard3.certificate.lower + (TermShard4.certificate.lower + (0))))))
  rw [TermShard0.certificate_lower, TermShard1.certificate_lower, TermShard2.certificate_lower, TermShard3.certificate_lower, TermShard4.certificate_lower]
  norm_num [lower, LowerBound.constant,
    TermShard0.lower, TermShard0.positiveFloor, TermShard0.negativeCeiling, TermShard0.constantNumerator, TermShard0.bits,
    TermShard1.lower, TermShard1.positiveFloor, TermShard1.negativeCeiling, TermShard1.constantNumerator, TermShard1.bits,
    TermShard2.lower, TermShard2.positiveFloor, TermShard2.negativeCeiling, TermShard2.constantNumerator, TermShard2.bits,
    TermShard3.lower, TermShard3.positiveFloor, TermShard3.negativeCeiling, TermShard3.constantNumerator, TermShard3.bits,
    TermShard4.lower, TermShard4.positiveFloor, TermShard4.negativeCeiling, TermShard4.constantNumerator, TermShard4.bits]

/-- The compositional shard checker bounds the semantic raw parent form. -/
theorem lower_le_expectedRaw_eval : lower ≤ Form.eval 116 expectedRaw := by
  rw [lower_eq_expectedCertificate_lower]
  unfold expectedCertificate
  calc
    _ ≤ Form.eval 116 (Form.sum rawForms) :=
      LowerBound.sum_lower_le_eval_sum_of_forall₂ expectedCertificates_eval_rawForms
    _ = Form.eval 116 expectedRaw :=
      congrArg (Form.eval 116) rawForms_sum_eq_expectedRaw

/-- Independent power extraction and structural canonicalization preserve the parent value. -/
theorem lower_le_expectedForm_eval : lower ≤ Form.eval 116 expectedForm := by
  calc
    _ ≤ Form.eval 116 expectedRaw := lower_le_expectedRaw_eval
    _ = Form.eval 116 expectedPower := by
      unfold expectedPower
      exact (Form.eval_normalizePowersOfTwo 116 expectedRaw).symm
    _ = Form.eval 116 expectedForm := by
      unfold expectedForm
      exact (Form.eval_structuralFastCanonical 116 expectedPower).symm

/-- Exact branch value contributed by this parent. -/
theorem rate_eq :
    branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows
        Orientation.order Weights.Region1.dualWeights 1 [parent] 1 =
      Form.eval 116 expectedForm := by
  have heval := congrArg (Form.eval 116) recurrence_structuralPowerCanonical
  rw [Form.eval_structuralPowerCanonical, branchFormOnParentsFrom_eval] at heval
  exact heval

/-- This parent's directed endpoint is below its reconstructed branch rate. -/
theorem lower_le_rate :
    lower ≤ branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows
      Orientation.order Weights.Region1.dualWeights 1 [parent] 1 := by
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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
