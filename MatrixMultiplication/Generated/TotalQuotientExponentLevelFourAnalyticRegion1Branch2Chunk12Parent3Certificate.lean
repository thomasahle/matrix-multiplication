import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTopData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourBetaThreeData
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourOrientation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourWeightsRegion1
import Mathlib.Data.List.SplitLengths
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12TermsParent3
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent3

/-! Independently sealed numeric certificate for level-four region 1, branch 2,
parent chunk 12, parent 53; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

/-- Constant-only raw form preceding the source-order logarithmic shards. -/
def rawBaseForm : Form := { constantNumerator := 0, terms := [] }

/-- Source-order raw logarithmic forms before independent power extraction. -/
def rawForms : List Form := [rawBaseForm, TermShard0.rawForm, TermShard1.rawForm, TermShard2.rawForm, TermShard3.rawForm, TermShard4.rawForm, TermShard5.rawForm, TermShard6.rawForm, TermShard7.rawForm, TermShard8.rawForm, TermShard9.rawForm, TermShard10.rawForm, TermShard11.rawForm, TermShard12.rawForm, TermShard13.rawForm]

/-- All certificate shards, including the exact source constant. -/
noncomputable def expectedCertificates : List (LowerBound 116) :=
  [LowerBound.constant 116 0, TermShard0.certificate, TermShard1.certificate, TermShard2.certificate, TermShard3.certificate, TermShard4.certificate, TermShard5.certificate, TermShard6.certificate, TermShard7.certificate, TermShard8.certificate, TermShard9.certificate, TermShard10.certificate, TermShard11.certificate, TermShard12.certificate, TermShard13.certificate]

/-- Compositional lower certificate assembled from the bounded numeric shards. -/
noncomputable def expectedCertificate : LowerBound 116 :=
  LowerBound.sum expectedCertificates

/-- Raw shard term lists in their original source order. -/
def rawTermChunks : List (List Term) := [TermShard0.rawForm.terms, TermShard1.rawForm.terms, TermShard2.rawForm.terms, TermShard3.rawForm.terms, TermShard4.rawForm.terms, TermShard5.rawForm.terms, TermShard6.rawForm.terms, TermShard7.rawForm.terms, TermShard8.rawForm.terms, TermShard9.rawForm.terms, TermShard10.rawForm.terms, TermShard11.rawForm.terms, TermShard12.rawForm.terms, TermShard13.rawForm.terms]

/-- Bounded chunk sizes used to recover the complete source term list. -/
def termChunkSizes : List ℕ := [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 58]

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
    TermShard4.rawForm.terms = (((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl
/-- Bounded source slice represented by raw shard 5. -/
theorem rawTermChunk5_eq :
    TermShard5.rawForm.terms = ((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl
/-- Bounded source slice represented by raw shard 6. -/
theorem rawTermChunk6_eq :
    TermShard6.rawForm.terms = (((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl
/-- Bounded source slice represented by raw shard 7. -/
theorem rawTermChunk7_eq :
    TermShard7.rawForm.terms = ((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl
/-- Bounded source slice represented by raw shard 8. -/
theorem rawTermChunk8_eq :
    TermShard8.rawForm.terms = (((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl
/-- Bounded source slice represented by raw shard 9. -/
theorem rawTermChunk9_eq :
    TermShard9.rawForm.terms = ((((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl
/-- Bounded source slice represented by raw shard 10. -/
theorem rawTermChunk10_eq :
    TermShard10.rawForm.terms = (((((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl
/-- Bounded source slice represented by raw shard 11. -/
theorem rawTermChunk11_eq :
    TermShard11.rawForm.terms = ((((((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl
/-- Bounded source slice represented by raw shard 12. -/
theorem rawTermChunk12_eq :
    TermShard12.rawForm.terms = (((((((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl
/-- Bounded source slice represented by raw shard 13. -/
theorem rawTermChunk13_eq :
    TermShard13.rawForm.terms = ((((((((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 58 := by
  rfl

/-- The semantic raw form has the serialized source constant. -/
theorem expectedRaw_constant : expectedRaw.constantNumerator = 0 := by
  rfl

/-- The semantic raw form has exactly the serialized number of logarithmic terms. -/
theorem expectedRaw_terms_length : expectedRaw.terms.length = 890 := by
  rfl

/-- The independently checked raw shards are exactly the bounded semantic source slices. -/
theorem rawTermChunks_eq_expectedRawTermChunks :
    rawTermChunks = expectedRawTermChunks := by
  unfold rawTermChunks expectedRawTermChunks termChunkSizes
  simp only [List.splitLengths_cons, List.splitLengths_nil]
  rw [rawTermChunk0_eq, rawTermChunk1_eq, rawTermChunk2_eq, rawTermChunk3_eq, rawTermChunk4_eq, rawTermChunk5_eq, rawTermChunk6_eq, rawTermChunk7_eq, rawTermChunk8_eq, rawTermChunk9_eq, rawTermChunk10_eq, rawTermChunk11_eq, rawTermChunk12_eq, rawTermChunk13_eq]

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
  norm_num [rawForms, rawBaseForm, TermShard0.rawForm_constant, TermShard1.rawForm_constant, TermShard2.rawForm_constant, TermShard3.rawForm_constant, TermShard4.rawForm_constant, TermShard5.rawForm_constant, TermShard6.rawForm_constant, TermShard7.rawForm_constant, TermShard8.rawForm_constant, TermShard9.rawForm_constant, TermShard10.rawForm_constant, TermShard11.rawForm_constant, TermShard12.rawForm_constant, TermShard13.rawForm_constant]

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
  · exact TermShard5.form_eval_rawForm
  constructor
  · exact TermShard6.form_eval_rawForm
  constructor
  · exact TermShard7.form_eval_rawForm
  constructor
  · exact TermShard8.form_eval_rawForm
  constructor
  · exact TermShard9.form_eval_rawForm
  constructor
  · exact TermShard10.form_eval_rawForm
  constructor
  · exact TermShard11.form_eval_rawForm
  constructor
  · exact TermShard12.form_eval_rawForm
  constructor
  · exact TermShard13.form_eval_rawForm
  constructor

/-- Directed rational endpoint after summing this parent's term-shard endpoints. -/
noncomputable def lower : ℝ := 1242741843098690574441649 / 17592186044416000000000000

/-- The serialized rational endpoint is exactly the compositional certificate endpoint. -/
theorem lower_eq_expectedCertificate_lower : lower = expectedCertificate.lower := by
  rw [expectedCertificate, LowerBound.sum_lower]
  change lower = (LowerBound.constant 116 0).lower + (TermShard0.certificate.lower + (TermShard1.certificate.lower + (TermShard2.certificate.lower + (TermShard3.certificate.lower + (TermShard4.certificate.lower + (TermShard5.certificate.lower + (TermShard6.certificate.lower + (TermShard7.certificate.lower + (TermShard8.certificate.lower + (TermShard9.certificate.lower + (TermShard10.certificate.lower + (TermShard11.certificate.lower + (TermShard12.certificate.lower + (TermShard13.certificate.lower + (0)))))))))))))))
  rw [TermShard0.certificate_lower, TermShard1.certificate_lower, TermShard2.certificate_lower, TermShard3.certificate_lower, TermShard4.certificate_lower, TermShard5.certificate_lower, TermShard6.certificate_lower, TermShard7.certificate_lower, TermShard8.certificate_lower, TermShard9.certificate_lower, TermShard10.certificate_lower, TermShard11.certificate_lower, TermShard12.certificate_lower, TermShard13.certificate_lower]
  norm_num [lower, LowerBound.constant,
    TermShard0.lower, TermShard0.positiveFloor, TermShard0.negativeCeiling, TermShard0.constantNumerator, TermShard0.bits,
    TermShard1.lower, TermShard1.positiveFloor, TermShard1.negativeCeiling, TermShard1.constantNumerator, TermShard1.bits,
    TermShard2.lower, TermShard2.positiveFloor, TermShard2.negativeCeiling, TermShard2.constantNumerator, TermShard2.bits,
    TermShard3.lower, TermShard3.positiveFloor, TermShard3.negativeCeiling, TermShard3.constantNumerator, TermShard3.bits,
    TermShard4.lower, TermShard4.positiveFloor, TermShard4.negativeCeiling, TermShard4.constantNumerator, TermShard4.bits,
    TermShard5.lower, TermShard5.positiveFloor, TermShard5.negativeCeiling, TermShard5.constantNumerator, TermShard5.bits,
    TermShard6.lower, TermShard6.positiveFloor, TermShard6.negativeCeiling, TermShard6.constantNumerator, TermShard6.bits,
    TermShard7.lower, TermShard7.positiveFloor, TermShard7.negativeCeiling, TermShard7.constantNumerator, TermShard7.bits,
    TermShard8.lower, TermShard8.positiveFloor, TermShard8.negativeCeiling, TermShard8.constantNumerator, TermShard8.bits,
    TermShard9.lower, TermShard9.positiveFloor, TermShard9.negativeCeiling, TermShard9.constantNumerator, TermShard9.bits,
    TermShard10.lower, TermShard10.positiveFloor, TermShard10.negativeCeiling, TermShard10.constantNumerator, TermShard10.bits,
    TermShard11.lower, TermShard11.positiveFloor, TermShard11.negativeCeiling, TermShard11.constantNumerator, TermShard11.bits,
    TermShard12.lower, TermShard12.positiveFloor, TermShard12.negativeCeiling, TermShard12.constantNumerator, TermShard12.bits,
    TermShard13.lower, TermShard13.positiveFloor, TermShard13.negativeCeiling, TermShard13.constantNumerator, TermShard13.bits]

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
        Orientation.order Weights.Region1.dualWeights 1 [parent] 2 =
      Form.eval 116 expectedForm := by
  have heval := congrArg (Form.eval 116) recurrence_structuralPowerCanonical
  rw [Form.eval_structuralPowerCanonical, branchFormOnParentsFrom_eval] at heval
  exact heval

/-- This parent's directed endpoint is below its reconstructed branch rate. -/
theorem lower_le_rate :
    lower ≤ branchRateOnParentsFrom Top.expectedRows BetaThree.expectedRows
      Orientation.order Weights.Region1.dualWeights 1 [parent] 2 := by
  rw [rate_eq]
  exact lower_le_expectedForm_eval

/-- The parent endpoint and exact form, packaged for chunk composition. -/
noncomputable def certificate : LowerBound 116 :=
  { form := expectedForm
    lower := lower
    lower_le_eval := lower_le_expectedForm_eval }

@[simp] theorem certificate_form : certificate.form = expectedForm := rfl
@[simp] theorem certificate_lower : certificate.lower = lower := rfl

end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
