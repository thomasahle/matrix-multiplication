/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicChordTangentCompression
import MatrixMultiplication.TotalWeightVolumeEndpoint

/-!
# The compression seam of the total-weight quotient retained exponent

`Generated/TotalQuotientExponentScalarData.lean` exposes one real number,
`retainedExponentLowerWitness`, and proves that it exceeds the directed rational floor
`8.2419803`.  What it does *not* prove — and says so in its own header — is that this witness is
below the semantic retained base-two copy exponent of the certificate.  That inequality is the
first conjunct of `TotalWeightVolumeEndpoint.Reconstruction`, and it splits into two independent
halves:

1. **compression** — the committed witness is at most the chord/tangent compression of the exact
   log-linear form the certificate evaluator produces; and
2. **evaluation** — the exact log-linear form is at most the semantic retained exponent.

Half 1 is settled here, generically and at any mantissa width, by
`LogLinearCompression.le_of_chordTangentCompression`: no property of the concrete arrays is used
beyond the bracketing facts a generated client discharges by `decide`.  Half 2 is the NPZ
decoder / recurrence-evaluator obligation; it appears below as the named hypothesis `hsemantic`
and is the only thing this file leaves open.

## What is proved here

* `RetainedCompressionSeam` — the seam as a one-line proposition, so that clients quote it
  instead of re-deriving the witness inequality.
* `retainedCompressionSeam_of_chordTangentCompression` — half 1: the seam follows from the
  compression relation together with half 2, with the compression itself no longer in the
  client's trust boundary.
* `inverseLogFloor_le_of_directedResidual` — the committed certificate's residual endpoint is an
  instance of the generic directed rule `inverseLogTwoFloor`, re-proving the emitted
  `inverseLogFloor_le` from the general lemma rather than from a per-certificate two-branch
  script.  The certificate's residual coefficient is positive, so its floor divides by an *upper*
  enclosure of `log 2`.
* `le_of_seam` and the four named consequences — every rational floor at most the committed
  directed floor `8.2419803` follows from the seam.  This covers the total-weight acceptance
  floor `8.22`, the tight endpoint's `baseRetainedLower = 8.200979373915867`, and the coarse
  `volumeOnlyRetainedLower = 8.2`, all with reserve of order `10⁻²` against a compression slack of
  order `10⁻⁷`.
* `omega_lt_236588731_of_compressionSeam` and `omega_lt_236999_of_compressionSeam` — the seam,
  a volume witness and an extraction sequence give the two endpoints outright.

## Position in the library

Paper layer (`MatrixMultiplication/`).  It adds no arithmetic of its own: the generic compression
lives in `DyadicChordTangentCompression.lean`, the certificate arithmetic in the generated module,
and the endpoint assembly in `TotalWeightVolumeEndpoint.lean`.
-/

namespace MatrixMultiplication.TotalQuotientRetainedCompressionSeam

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.LogLinearCompression
open MatrixMultiplication.Generated.TotalQuotientExponentScalar

universe u v

/-- **The seam.**  The committed compressed witness of the total-weight quotient certificate is at
most the semantic retained base-two copy exponent.

This is exactly the first conjunct of `TotalWeightVolumeEndpoint.Reconstruction`; naming it
separates the numeric obligation from the volume obligation, which is settled by a different
generated module and needs no compression at all. -/
def RetainedCompressionSeam (semanticRetained : ℝ) : Prop :=
  retainedExponentLowerWitness ≤ semanticRetained

/-- **Half one of the seam, discharged.**  If the committed witness is at most the chord/tangent
compression of a signed log-linear form, and the exact value of that form is at most the semantic
retained exponent, then the seam holds.

Every hypothesis except `hsemantic` is a finite check on the emitted arrays: nonnegativity of the
weights, positivity of the endpoints and centres, and the bracketing of each argument by its bin.
`hsemantic` is the NPZ decoder / recurrence evaluator obligation of stage N1. -/
theorem retainedCompressionSeam_of_chordTangentCompression
    {Item ItemNeg : Type u} {Bin BinNeg : Type v}
    [Fintype Item] [Fintype ItemNeg] [Fintype Bin] [Fintype BinNeg]
    [DecidableEq Bin] [DecidableEq BinNeg]
    {semanticRetained : ℝ}
    (constant : ℝ)
    (positiveBin : Item → Bin) (positiveWeight positiveArgument : Item → ℝ)
    (lower upper : Bin → ℝ)
    (negativeBin : ItemNeg → BinNeg) (negativeWeight negativeArgument : ItemNeg → ℝ)
    (center : BinNeg → ℝ)
    (hpositiveWeight : ∀ item, 0 ≤ positiveWeight item)
    (hlower : ∀ b, 0 < lower b)
    (hlowerLe : ∀ item, lower (positiveBin item) ≤ positiveArgument item)
    (hleUpper : ∀ item, positiveArgument item ≤ upper (positiveBin item))
    (hlowerLtUpper : ∀ b, lower b < upper b)
    (hnegativeWeight : ∀ item, 0 ≤ negativeWeight item)
    (hnegativeArgument : ∀ item, 0 < negativeArgument item)
    (hcenter : ∀ b, 0 < center b)
    (hwitness : retainedExponentLowerWitness ≤
      chordTangentValue constant positiveBin positiveWeight positiveArgument lower upper
        negativeBin negativeWeight negativeArgument center)
    (hsemantic :
      exactValue constant positiveWeight positiveArgument negativeWeight negativeArgument ≤
        semanticRetained) :
    RetainedCompressionSeam semanticRetained :=
  le_of_chordTangentCompression constant positiveBin positiveWeight positiveArgument lower upper
    negativeBin negativeWeight negativeArgument center hpositiveWeight hlower hlowerLe hleUpper
    hlowerLtUpper hnegativeWeight hnegativeArgument hcenter hwitness hsemantic

/-! ## The committed residual endpoint as an instance of the generic directed rule -/

/-- The certificate's residual coefficient is positive. -/
theorem inverseLogCoefficient_nonneg : (0 : ℝ) ≤ inverseLogCoefficient := by
  norm_num [inverseLogCoefficient]

/-- The committed residual floor is the generic directed endpoint at the fast `log 2` enclosures:
because the coefficient is positive, the floor divides by the *upper* enclosure. -/
theorem inverseLogFloor_le_inverseLogTwoFloor :
    inverseLogFloor ≤
      inverseLogTwoFloor inverseLogCoefficient
        MatrixMultiplication.FastDyadicLog.fastLogTwoLower
        MatrixMultiplication.FastDyadicLog.fastLogTwoUpper := by
  rw [inverseLogTwoFloor_of_nonneg inverseLogCoefficient_nonneg]
  norm_num [inverseLogFloor, inverseLogCoefficient,
    MatrixMultiplication.FastDyadicLog.fastLogTwoUpper]

/-- **The emitted residual proof, re-derived from the general lemma.**  The exporter currently
emits a two-branch script per certificate; this shows the branch it chose is the generic
`inverseLogTwoFloor_le` specialized at the fast `log 2` enclosures. -/
theorem inverseLogFloor_le_of_directedResidual : inverseLogFloor ≤ inverseLogTerm := by
  have hlowerPos : (0 : ℝ) < MatrixMultiplication.FastDyadicLog.fastLogTwoLower := by
    norm_num [MatrixMultiplication.FastDyadicLog.fastLogTwoLower]
  have hlower : MatrixMultiplication.FastDyadicLog.fastLogTwoLower ≤ Real.log 2 :=
    MatrixMultiplication.FastDyadicLog.fastLogTwoLower_le_logTwoLower.trans
      MatrixMultiplication.LogBounds.logTwoLower_le_logTwo
  have hupper : Real.log 2 ≤ MatrixMultiplication.FastDyadicLog.fastLogTwoUpper :=
    MatrixMultiplication.LogBounds.logTwo_le_logTwoUpper.trans
      MatrixMultiplication.FastDyadicLog.logTwoUpper_le_fastLogTwoUpper
  exact inverseLogFloor_le_inverseLogTwoFloor.trans
    (inverseLogTwoFloor_le hlowerPos hlower hupper)

/-! ## Consequences of the seam -/

/-- Every rational floor at most the committed directed floor `8.2419803` is below the semantic
retained exponent once the seam holds. -/
theorem le_of_seam {floor semanticRetained : ℝ}
    (hfloor : floor ≤ retainedExponentFloor)
    (hseam : RetainedCompressionSeam semanticRetained) :
    floor ≤ semanticRetained :=
  (hfloor.trans retainedExponentFloor_lt_retainedExponentLowerWitness.le).trans hseam

/-- The total-weight acceptance floor `8.22`, with reserve `2.19803e-02` against the committed
directed floor — five orders of magnitude above the `1.97e-07` compression slack. -/
theorem acceptanceRetainedFloor_le_of_seam {semanticRetained : ℝ}
    (hseam : RetainedCompressionSeam semanticRetained) :
    TotalWeightVolumeEndpoint.acceptanceRetainedFloor ≤ semanticRetained :=
  le_of_seam (by
    norm_num [TotalWeightVolumeEndpoint.acceptanceRetainedFloor, retainedExponentFloor]) hseam

/-- The coarse volume-only retained floor `8.2`, with reserve `4.19803e-02`. -/
theorem volumeOnlyRetainedLower_le_of_seam {semanticRetained : ℝ}
    (hseam : RetainedCompressionSeam semanticRetained) :
    MatrixMultiplication.CurrentProofObligations.volumeOnlyRetainedLower ≤ semanticRetained :=
  le_of_seam (by
    norm_num [MatrixMultiplication.CurrentProofObligations.volumeOnlyRetainedLower,
      retainedExponentFloor]) hseam

/-- The tight endpoint's retained floor `8.200979373915867`, with reserve `4.10009e-02`.  The
compression slack is therefore not what stands between this certificate and the tight target. -/
theorem baseRetainedLower_le_of_seam {semanticRetained : ℝ}
    (hseam : RetainedCompressionSeam semanticRetained) :
    MatrixMultiplication.CurrentProofObligations.baseRetainedLower ≤ semanticRetained :=
  le_of_seam (by
    norm_num [MatrixMultiplication.CurrentProofObligations.baseRetainedLower,
      retainedExponentFloor]) hseam

/-- The certificate's own directed floor. -/
theorem retainedFloor_le_of_seam {semanticRetained : ℝ}
    (hseam : RetainedCompressionSeam semanticRetained) :
    TotalWeightVolumeEndpoint.retainedFloor ≤ semanticRetained :=
  le_of_seam le_rfl hseam

/-- The seam is exactly the retained half of `TotalWeightVolumeEndpoint.Reconstruction`. -/
theorem reconstruction_of_seam {retained volume : ℝ}
    (hretained : RetainedCompressionSeam retained)
    (hvolume :
      MatrixMultiplication.Generated.TotalQuotientVolumeScalar.scalarCoordinateSum / 3 ≤ volume) :
    TotalWeightVolumeEndpoint.Reconstruction retained volume :=
  ⟨hretained, hvolume⟩

/-- The exact total-weight endpoint, from the seam and a volume witness. -/
theorem omega_lt_236588731_of_compressionSeam
    (K : Type u) [Field K] {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hretained : RetainedCompressionSeam retained)
    (hvolume :
      MatrixMultiplication.Generated.TotalQuotientVolumeScalar.scalarCoordinateSum / 3 ≤ volume) :
    omega K < TotalWeightVolumeEndpoint.omegaTarget :=
  TotalWeightVolumeEndpoint.omega_lt_236588731_of_subexponentialVolumeSequence K hextractions
    (reconstruction_of_seam hretained hvolume)

/-- The requested `2.36999` milestone, from the same two inputs. -/
theorem omega_lt_236999_of_compressionSeam
    (K : Type u) [Field K] {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hretained : RetainedCompressionSeam retained)
    (hvolume :
      MatrixMultiplication.Generated.TotalQuotientVolumeScalar.scalarCoordinateSum / 3 ≤ volume) :
    omega K < TotalWeightVolumeEndpoint.acceptanceTarget :=
  TotalWeightVolumeEndpoint.omega_lt_236999_of_subexponentialVolumeSequence K hextractions
    (reconstruction_of_seam hretained hvolume)

end MatrixMultiplication.TotalQuotientRetainedCompressionSeam
