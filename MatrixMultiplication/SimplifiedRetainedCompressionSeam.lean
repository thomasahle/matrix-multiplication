/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicMantissaNormalization
import MatrixMultiplication.Generated.SimplifiedExponentCoarseFloors
import MatrixMultiplication.SimplifiedSharpEndpoint

/-!
# The compression seam of the simplified certificate's retained exponent

`Generated/SimplifiedExponentScalarData.lean` is the retained-side payload of the certificate with
SHA-256 `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082` — the certificate the
volume-only `2.36999` milestone is fed by.  It exposes one real number,
`retainedExponentLowerWitness`, and proves that it exceeds the rational floor
`8.200197314999464…`.  What it does *not* prove — and says so in its own header — is that this
witness is below the semantic retained base-two copy exponent.  That inequality splits into two
independent halves:

1. **compression** — the committed witness is at most the chord/tangent compression of the exact
   log-linear form the certificate evaluator produces; and
2. **evaluation** — the exact log-linear form is at most the semantic retained exponent.

Half 1 is settled here, generically and at any mantissa width, by
`LogLinearCompression.le_of_chordTangentCompression` together with the odd-mantissa normalization
identity `LogLinearCompression.chordTangentValue_eq_normalized`: no property of the concrete
arrays survives into the client's trust boundary except finite rational identities on the emitted
coefficients.  Half 2 is the NPZ decoder / recurrence-evaluator obligation of stage N1; it appears
below as the named hypothesis `hsemantic` and is the only thing this file leaves open.

This is the simplified-track mirror of
`MatrixMultiplication/TotalQuotientRetainedCompressionSeam.lean`, and the two certificates differ
in exactly one structural way: the total-weight quotient's residual coefficient is **positive**,
the simplified certificate's is **negative**.  So the directed rule `inverseLogTwoFloor` is
exercised here on its other branch — the floor divides by a *lower* enclosure of `log 2` — and
`inverseLogFloor_le_of_directedResidual` re-proves the emitted two-branch script from the generic
lemma on that branch.

## What is proved here

* `RetainedCompressionSeam` — the seam as a one-line proposition, so that clients quote it instead
  of re-deriving the witness inequality.  It is the first conjunct of
  `SimplifiedSharpEndpoint.Reconstruction`.
* `retainedExponentLowerWitness_eq_exactValue` — the committed payload read in the generic
  vocabulary: the emitted odd-mantissa arrays *are* a signed log-linear form, and the witness is
  its exact value plus the residual.
* `retainedCompressionSeam_of_chordTangentCompression` — half 1 in the raw form: the seam follows
  from a compression relation plus half 2.
* `retainedCompressionSeam_of_normalizedChordTangentCompression` — **half 1 with the witness
  inequality discharged**: the emitter identity is replaced by four finite identities on the
  emitted arrays (one constant, two coefficient families, one residual) plus the `decide`-level
  factorization of each bin endpoint and centre into `2 ^ k ·` odd mantissa.  Nothing but
  `hsemantic` is left open.
* `inverseLogFloor_le_of_directedResidual` — the emitted residual endpoint as an instance of the
  generic directed rule, on the negative branch.
* `le_of_seam` and its three named consequences — every rational floor at most the committed
  rational floor follows from the seam.  This covers the coarse volume-only
  `volumeOnlyRetainedLower = 8.2` with reserve `1.97315e-04`, and the four-family coarse floor
  `8.200174` with reserve `2.3315e-05`, against a compression slack of order `2.4e-04` that the
  emitted floor has already paid.
* `volumeOnlyLevelFourReconstruction_of_seam` and `omega_lt_236999_of_compressionSeam` — the
  milestone predicate and endpoint, from the seam and a volume witness.

## Honest limits of this certificate

The eab2c7 retained witness clears `8.2`, but **not** the tight
`CurrentProofObligations.baseRetainedLower = 8.200979373915867` (it falls short by `7.82e-04`) and
not the total-weight acceptance floor `8.22`.  Those endpoints belong to the deeper certificates;
the simplified track is the volume-only milestone's certificate, and this module deliberately
proves only the floors it actually reaches.

## STATUS — the certificate is REFUTED for endpoint use; the module is the generic template

**Corrected 2026-08-28 (commit `8a8e110`'s analysis).**  The eab2c7 retained exponent `8.200434`
that the payload above compresses is an artifact of the **ARCHIVED (uncorrected)** evaluator
complement table; under the corrected table the same certificate gives `8.160594`, which is
**below** `volumeOnlyRetainedLower = 8.2` by `3.94e-02`.  So the one hypothesis this file leaves
open, `hsemantic`, is not merely unproved on eab2c7 — it is **false** there, and neither
`volumeOnlyLevelFourReconstruction_of_seam` nor `omega_lt_236999_of_compressionSeam` may ever be
instantiated at this certificate.  Everything below stays true exactly as stated, because it is all
conditional on `hsemantic`.

What the module is *for*, therefore: it is the **generic template** — its
`retainedCompressionSeam_of_normalizedChordTangentCompression` is the shape transcribed onto the
sound total-weight (e7987) payload in
`MatrixMultiplication/TotalQuotientRetainedCompressionSeam.lean` and
`MatrixMultiplication/TotalQuotientNormalizedCompression.lean`, whose retained exponent
`8.241980527215809` reproduces under the corrected table.  Live retained-side work belongs there.
The generated payload it reads is listed in `scripts/artifact_provenance_quarantine.txt` and this
module is one of the three consumers grandfathered by
`scripts/check_artifact_provenance.sh`; no new client may be added.
-/

namespace MatrixMultiplication.SimplifiedRetainedCompressionSeam

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.LogLinearCompression
open MatrixMultiplication.Generated.SimplifiedExponentScalar

universe u v

noncomputable section

/-- **The seam.**  The committed compressed witness of the simplified certificate is at most the
semantic retained base-two copy exponent.

This is exactly the first conjunct of `SimplifiedSharpEndpoint.Reconstruction`; naming it
separates the numeric obligation from the volume obligation, which is settled by a different
generated module and needs no compression at all. -/
def RetainedCompressionSeam (semanticRetained : ℝ) : Prop :=
  retainedExponentLowerWitness ≤ semanticRetained

/-! ## The committed payload in the generic vocabulary -/

/-- Real weight of one committed positive odd mantissa. -/
def positiveWeight (term : Positive0.Term) : ℝ := mass bits (Positive0.coefficient term)

/-- Real value of one committed positive odd mantissa. -/
def positiveArgument (term : Positive0.Term) : ℝ := (Positive0.argument term : ℝ)

/-- Real weight of one committed negative odd mantissa. -/
def negativeWeight (term : Negative0.Term) : ℝ := mass bits (Negative0.coefficient term)

/-- Real value of one committed negative odd mantissa. -/
def negativeArgument (term : Negative0.Term) : ℝ := (Negative0.argument term : ℝ)

theorem positiveArgument_pos : ∀ term, 0 < positiveArgument term := by
  intro term
  have := Positive0.arguments_pos term
  unfold positiveArgument
  exact_mod_cast this

theorem negativeArgument_pos : ∀ term, 0 < negativeArgument term := by
  intro term
  have := Negative0.arguments_pos term
  unfold negativeArgument
  exact_mod_cast this

/-- **The committed payload is a signed log-linear form.**  The generated module stores a dyadic
constant, one nonnegative coefficient per odd mantissa below `2 ^ 7`, one per odd mantissa between
`2 ^ 7` and `2 ^ 8`, and a single residual coefficient of `1 / log 2`; the witness is the exact
value of that form plus the residual term.

Purely definitional, but it is what lets the emitter identity below be stated entirely inside the
generic compression vocabulary. -/
theorem retainedExponentLowerWitness_eq_exactValue :
    retainedExponentLowerWitness =
      exactValue (mass bits constantNumerator) positiveWeight positiveArgument
          negativeWeight negativeArgument +
        inverseLogTerm := by
  unfold retainedExponentLowerWitness positiveExactSum negativeExactSum exactValue
    positiveWeight positiveArgument negativeWeight negativeArgument
  simp only [Positive0.exact, Negative0.exact, MatrixMultiplication.DyadicLogLinear.logSum, bits]

/-! ## Half one of the seam -/

/-- **Half one of the seam, raw form.**  If the committed witness is at most the chord/tangent
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
    (positiveBin : Item → Bin) (positiveItemWeight positiveItemArgument : Item → ℝ)
    (lower upper : Bin → ℝ)
    (negativeBin : ItemNeg → BinNeg) (negativeItemWeight negativeItemArgument : ItemNeg → ℝ)
    (center : BinNeg → ℝ)
    (hpositiveWeight : ∀ item, 0 ≤ positiveItemWeight item)
    (hlower : ∀ b, 0 < lower b)
    (hlowerLe : ∀ item, lower (positiveBin item) ≤ positiveItemArgument item)
    (hleUpper : ∀ item, positiveItemArgument item ≤ upper (positiveBin item))
    (hlowerLtUpper : ∀ b, lower b < upper b)
    (hnegativeWeight : ∀ item, 0 ≤ negativeItemWeight item)
    (hnegativeArgument : ∀ item, 0 < negativeItemArgument item)
    (hcenter : ∀ b, 0 < center b)
    (hwitness : retainedExponentLowerWitness ≤
      chordTangentValue constant positiveBin positiveItemWeight positiveItemArgument lower upper
        negativeBin negativeItemWeight negativeItemArgument center)
    (hsemantic :
      exactValue constant positiveItemWeight positiveItemArgument
          negativeItemWeight negativeItemArgument ≤
        semanticRetained) :
    RetainedCompressionSeam semanticRetained :=
  le_of_chordTangentCompression constant positiveBin positiveItemWeight positiveItemArgument
    lower upper negativeBin negativeItemWeight negativeItemArgument center hpositiveWeight
    hlower hlowerLe hleUpper hlowerLtUpper hnegativeWeight hnegativeArgument hcenter hwitness
    hsemantic

/-- **Half one of the seam, with the emitter identity discharged.**

The exporter's last step regroups the chord expansion onto odd mantissas
(`normalize_power_of_two_factors`).  By `chordTangentValue_eq_normalized` that regrouping is an
exact identity, so the witness inequality of the previous theorem becomes four finite statements
about the emitted arrays — no logarithm, no re-indexing, no analysis:

* `hendpointFactor`, `hcenterFactor` — each bin endpoint and each bin centre is `2 ^ k` times one
  of the committed odd mantissas (a `decide` on ℕ arrays);
* `hconstant` — the committed dyadic constant is the form's constant plus the two valuation
  shifts;
* `hpositiveCoefficient`, `hnegativeCoefficient` — each committed coefficient is the fiber sum of
  the chord/pooling coefficients landing on that mantissa;
* `hresidual` — the committed residual coefficient is the pooled first-order error.

What remains open is exactly `hsemantic`, stage N1's evaluator identification. -/
theorem retainedCompressionSeam_of_normalizedChordTangentCompression
    {Item ItemNeg : Type u} {Bin BinNeg : Type v}
    [Fintype Item] [Fintype ItemNeg] [Fintype Bin] [Fintype BinNeg]
    [DecidableEq Bin] [DecidableEq BinNeg]
    {semanticRetained : ℝ}
    (constant : ℝ)
    (positiveBin : Item → Bin) (positiveItemWeight positiveItemArgument : Item → ℝ)
    (lower upper : Bin → ℝ)
    (negativeBin : ItemNeg → BinNeg) (negativeItemWeight negativeItemArgument : ItemNeg → ℝ)
    (center : BinNeg → ℝ)
    (endpointValuation : Bin ⊕ Bin → ℕ) (endpointMantissa : Bin ⊕ Bin → Positive0.Term)
    (centerValuation : BinNeg → ℕ) (centerMantissa : BinNeg → Negative0.Term)
    (hendpointFactor : ∀ x, Sum.elim lower upper x =
      (2 : ℝ) ^ endpointValuation x * positiveArgument (endpointMantissa x))
    (hcenterFactor : ∀ b, center b =
      (2 : ℝ) ^ centerValuation b * negativeArgument (centerMantissa b))
    (hconstant : mass bits constantNumerator =
      constant +
          valuationShift
            (Sum.elim
              (chordLowerCoefficient positiveBin positiveItemWeight positiveItemArgument
                lower upper)
              (chordUpperCoefficient positiveBin positiveItemWeight positiveItemArgument
                lower upper))
            endpointValuation -
        valuationShift (fiberSum negativeBin negativeItemWeight) centerValuation)
    (hpositiveCoefficient : positiveWeight =
      fiberSum endpointMantissa
        (Sum.elim
          (chordLowerCoefficient positiveBin positiveItemWeight positiveItemArgument lower upper)
          (chordUpperCoefficient positiveBin positiveItemWeight positiveItemArgument
            lower upper)))
    (hnegativeCoefficient : negativeWeight =
      fiberSum centerMantissa (fiberSum negativeBin negativeItemWeight))
    (hresidual : inverseLogCoefficient =
      tangentResidual negativeBin negativeItemWeight negativeItemArgument center)
    (hpositiveWeight : ∀ item, 0 ≤ positiveItemWeight item)
    (hlower : ∀ b, 0 < lower b)
    (hlowerLe : ∀ item, lower (positiveBin item) ≤ positiveItemArgument item)
    (hleUpper : ∀ item, positiveItemArgument item ≤ upper (positiveBin item))
    (hlowerLtUpper : ∀ b, lower b < upper b)
    (hnegativeWeight : ∀ item, 0 ≤ negativeItemWeight item)
    (hnegativeArgument : ∀ item, 0 < negativeItemArgument item)
    (hcenter : ∀ b, 0 < center b)
    (hsemantic :
      exactValue constant positiveItemWeight positiveItemArgument
          negativeItemWeight negativeItemArgument ≤
        semanticRetained) :
    RetainedCompressionSeam semanticRetained := by
  refine retainedCompressionSeam_of_chordTangentCompression constant positiveBin
    positiveItemWeight positiveItemArgument lower upper negativeBin negativeItemWeight
    negativeItemArgument center hpositiveWeight hlower hlowerLe hleUpper hlowerLtUpper
    hnegativeWeight hnegativeArgument hcenter ?_ hsemantic
  rw [chordTangentValue_eq_normalized constant positiveBin positiveItemWeight positiveItemArgument
      lower upper negativeBin negativeItemWeight negativeItemArgument center
      endpointValuation endpointMantissa positiveArgument centerValuation centerMantissa
      negativeArgument positiveArgument_pos negativeArgument_pos hendpointFactor hcenterFactor,
    retainedExponentLowerWitness_eq_exactValue, hconstant, hpositiveCoefficient,
    hnegativeCoefficient]
  unfold inverseLogTerm
  rw [hresidual]

/-! ## The committed residual endpoint as an instance of the generic directed rule -/

/-- The simplified certificate's residual coefficient is negative — the branch the total-weight
quotient certificate never exercises. -/
theorem inverseLogCoefficient_neg : inverseLogCoefficient < 0 := by
  norm_num [inverseLogCoefficient]

/-- The committed residual floor is the generic directed endpoint at the fast `log 2` enclosures:
because the coefficient is negative, the floor divides by the *lower* enclosure. -/
theorem inverseLogFloor_le_inverseLogTwoFloor :
    inverseLogFloor ≤
      inverseLogTwoFloor inverseLogCoefficient
        MatrixMultiplication.FastDyadicLog.fastLogTwoLower
        MatrixMultiplication.FastDyadicLog.fastLogTwoUpper := by
  rw [inverseLogTwoFloor_of_neg inverseLogCoefficient_neg]
  norm_num [inverseLogFloor, inverseLogCoefficient,
    MatrixMultiplication.FastDyadicLog.fastLogTwoLower]

/-- **The emitted residual proof, re-derived from the general lemma.**  The exporter emits a
two-branch script per certificate; this shows the branch it chose here is the generic
`inverseLogTwoFloor_le` specialized at the fast `log 2` enclosures, on the negative branch. -/
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

/-- Every rational floor at most the committed rational floor `8.200197314999464…` is below the
semantic retained exponent once the seam holds. -/
theorem le_of_seam {floor semanticRetained : ℝ}
    (hfloor : floor ≤ MatrixMultiplication.SimplifiedSharpEndpoint.retainedFloor)
    (hseam : RetainedCompressionSeam semanticRetained) :
    floor ≤ semanticRetained :=
  (hfloor.trans MatrixMultiplication.SimplifiedSharpEndpoint.retainedFloor_le_witness).trans hseam

/-- The coarse volume-only retained floor `8.2`, with reserve `1.97315e-04`. -/
theorem volumeOnlyRetainedLower_le_of_seam {semanticRetained : ℝ}
    (hseam : RetainedCompressionSeam semanticRetained) :
    MatrixMultiplication.CurrentProofObligations.volumeOnlyRetainedLower ≤ semanticRetained :=
  le_of_seam (by
    norm_num [MatrixMultiplication.CurrentProofObligations.volumeOnlyRetainedLower,
      MatrixMultiplication.SimplifiedSharpEndpoint.retainedFloor]) hseam

/-- The four independently rounded family floors of the same certificate sum to `8.200174`, and
that too is below the aggregate witness, with reserve `2.3315e-05`.  So the two eab2c7 retained
routes — one aggregate log-linear form, four separately rounded families — are consistent, and
the aggregate one is the sharper of the two. -/
theorem coarseFourFamilyFloor_le_of_seam {semanticRetained : ℝ}
    (hseam : RetainedCompressionSeam semanticRetained) :
    MatrixMultiplication.Generated.SimplifiedExponentCoarseFloors.coarseFourFamilyFloor ≤
      semanticRetained :=
  le_of_seam (by
    rw [MatrixMultiplication.Generated.SimplifiedExponentCoarseFloors.coarseFourFamilyFloor_eq]
    norm_num [MatrixMultiplication.SimplifiedSharpEndpoint.retainedFloor]) hseam

/-- The certificate's own rational floor. -/
theorem retainedFloor_le_of_seam {semanticRetained : ℝ}
    (hseam : RetainedCompressionSeam semanticRetained) :
    MatrixMultiplication.SimplifiedSharpEndpoint.retainedFloor ≤ semanticRetained :=
  le_of_seam le_rfl hseam

/-! ## The milestone predicate and its endpoints -/

/-- **The milestone's reconstruction predicate, from the seam.**  Pairing the seam with any volume
witness above `volumeOnlyVolumeLower` discharges
`CurrentProofObligations.VolumeOnlyLevelFourReconstruction` — the reconstruction hypothesis of
`omega_lt_236999_of_volumeOnly_proof_obligations`. -/
theorem volumeOnlyLevelFourReconstruction_of_seam {retained volume : ℝ}
    (hseam : RetainedCompressionSeam retained)
    (hvolume : MatrixMultiplication.CurrentProofObligations.volumeOnlyVolumeLower ≤ volume) :
    MatrixMultiplication.CurrentProofObligations.VolumeOnlyLevelFourReconstruction
      retained volume :=
  ⟨volumeOnlyRetainedLower_le_of_seam hseam, hvolume⟩

/-- The seam is exactly the retained half of `SimplifiedSharpEndpoint.Reconstruction`. -/
theorem sharpReconstruction_of_seam {retained volume : ℝ}
    (hseam : RetainedCompressionSeam retained)
    (hvolume : MatrixMultiplication.SimplifiedSharpEndpoint.volumeFloor ≤ volume) :
    MatrixMultiplication.SimplifiedSharpEndpoint.Reconstruction retained volume :=
  ⟨hseam, hvolume⟩

/-- **The requested `2.36999` milestone, from the seam and a volume witness.** -/
theorem omega_lt_236999_of_compressionSeam
    (K : Type u) [Field K] {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hseam : RetainedCompressionSeam retained)
    (hvolume : MatrixMultiplication.CurrentProofObligations.volumeOnlyVolumeLower ≤ volume) :
    omega K < MatrixMultiplication.CurrentProofObligations.volumeOnlyOmegaTarget :=
  MatrixMultiplication.CurrentProofObligations.omega_lt_236999_of_subexponentialVolumeSequence
    K hextractions (volumeOnlyLevelFourReconstruction_of_seam hseam hvolume)

/-- The sharper `2.369837225` endpoint of the same certificate, from the same two inputs. -/
theorem omega_lt_2369837225_of_compressionSeam
    (K : Type u) [Field K] {stride : ℕ} {retained volume : ℝ}
    (hextractions : SubexponentialLaserVolumeSequence K
      (Tensor.power (coppersmithWinograd K 5) 8) stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hseam : RetainedCompressionSeam retained)
    (hvolume : MatrixMultiplication.SimplifiedSharpEndpoint.volumeFloor ≤ volume) :
    omega K < MatrixMultiplication.SimplifiedSharpEndpoint.omegaTarget :=
  MatrixMultiplication.SimplifiedSharpEndpoint.omega_lt_2369837225_of_subexponentialVolumeSequence
    K hextractions (sharpReconstruction_of_seam hseam hvolume)

end

end MatrixMultiplication.SimplifiedRetainedCompressionSeam
