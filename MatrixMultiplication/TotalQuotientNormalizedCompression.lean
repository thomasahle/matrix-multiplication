/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.LogLinearRationalAccumulation
import MatrixMultiplication.TotalQuotientRetainedCompressionSeam

/-!
# The emitter identity on the total-weight quotient's chunked retained payload

`TotalQuotientRetainedCompressionSeam.lean` reduces the retained half of the total-weight quotient
endpoint to `RetainedCompressionSeam`, and discharges that from a *compression relation*
`hwitness` together with the evaluator obligation `hsemantic`.  This module removes `hwitness`
from the client's trust boundary, as `SimplifiedRetainedCompressionSeam.lean` does on the
simplified track: the exporter's last step — `normalize_power_of_two_factors`, the regrouping of
every surviving logarithm argument `2 ^ k · m` onto its odd mantissa `m` — is an exact identity
(`LogLinearCompression.chordTangentValue_eq_normalized`), so the witness inequality becomes four
*finite rational* statements about the committed arrays plus one `decide`-level factorization per
bin endpoint and centre.

## The one structural difference from the simplified transcription

The simplified payload keeps its odd mantissas in a single positive and a single negative chunk,
so its mantissa index is one `Fin`.  The committed total-weight payload
`Generated/TotalQuotientExponentScalar*` is emitted in **17 positive and 16 negative chunks** (64
mantissas each except the last two, 47 and 39; 1071 positive and 999 negative mantissas, 2070
buckets in all).  The mantissa index of this seam is therefore *global*: the disjoint union
`PositiveTerm` / `NegativeTerm` of the committed chunk index types, with the committed arrays
dispatched over it.  `positiveExactSum_eq_sum` / `negativeExactSum_eq_sum` prove that the global
sum is the committed chunk-by-chunk sum, which is what lets the payload be read as a single signed
log-linear form.

## Why this certificate

Certificate `e7987d7f…` under the complete-split total-weight quotient `2:1=0|0;2:2=0|0|0;2:3=0|0`
reproduces bit-for-bit under the corrected evaluator complement table: its retained exponent is
`8.241980527215809` and the compressed witness `8.241980330293170`, so the committed directed
floor `8.2419803` clears `CurrentProofObligations.volumeOnlyRetainedLower = 8.2` by `4.198e-02`,
the tight `baseRetainedLower = 8.200979373915867` by `4.100e-02`, and the total-weight acceptance
floor `8.22` by `2.198e-02` — all against a compression slack of order `10⁻⁷`.  Those four
consequences are proved in the seam module; this module supplies the missing half of `hwitness`.

## What is proved here

* `PositiveTerm`, `NegativeTerm`, `positiveWeight`, `positiveArgument`, `negativeWeight`,
  `negativeArgument` — the committed chunked payload as one signed log-linear form, with the
  positivity of every argument inherited from the per-chunk `arguments_pos`.
* `positiveExactSum_eq_sum`, `negativeExactSum_eq_sum`,
  `retainedExponentLowerWitness_eq_exactValue` — the committed witness *is* the exact value of
  that form plus the single residual multiple of `1 / log 2`.
* `retainedCompressionSeam_of_normalizedChordTangentCompression` — **the deliverable**: the seam
  from four finite identities (`hconstant`, `hpositiveCoefficient`, `hnegativeCoefficient`,
  `hresidual`), the two `2 ^ k · odd` factorizations, the bracketing facts, and `hsemantic`.
  Nothing analytic is left in it, and `hsemantic` (stage N1) is the only genuinely open input.
* `mass_eq_ratCast` — the committed dyadic constant as an explicit rational cast, the entry point
  of the `ℚ`-level route of `LogLinearRationalAccumulation.lean`.
* `positiveWeight_eq_of_chunks`, `negativeWeight_eq_of_chunks` — the chunked-accumulation
  skeleton: the two coefficient-family identities assembled from one named finite fact per
  committed chunk (17 and 16 of them), so that a future per-chunk integral accumulation plugs in
  here without restating the seam.

## Position in the library

Paper layer (`MatrixMultiplication/`), directly above `TotalQuotientRetainedCompressionSeam.lean`
and `LogLinearRationalAccumulation.lean`.  It adds no arithmetic of its own: the compression and
its normalization are generic, the certificate arithmetic is in the generated modules, and the
endpoint assembly is in `TotalWeightVolumeEndpoint.lean`.
-/

set_option autoImplicit false

namespace MatrixMultiplication.TotalQuotientNormalizedCompression

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.LogLinearCompression
open MatrixMultiplication.TotalQuotientRetainedCompressionSeam
open MatrixMultiplication.Generated.TotalQuotientExponentScalar

universe u v

noncomputable section

/-! ## The global mantissa index

The committed payload is chunked, so the mantissa index of the whole form is the disjoint union of
the committed chunk index types.  `Sum.elim_inl` / `Sum.elim_inr` are `simp` lemmas, so a client
that names a chunk embedding reduces every definition below to that chunk's committed array.
-/

/-- Global positive mantissa index: the disjoint union of the 17 committed positive chunks
(1071 odd mantissas). -/
abbrev PositiveTerm : Type :=
  Positive0.Term ⊕ Positive1.Term ⊕ Positive2.Term ⊕ Positive3.Term ⊕
    Positive4.Term ⊕ Positive5.Term ⊕ Positive6.Term ⊕ Positive7.Term ⊕
    Positive8.Term ⊕ Positive9.Term ⊕ Positive10.Term ⊕ Positive11.Term ⊕
    Positive12.Term ⊕ Positive13.Term ⊕ Positive14.Term ⊕ Positive15.Term ⊕
    Positive16.Term

/-- Global negative mantissa index: the disjoint union of the 16 committed negative chunks
(999 odd mantissas). -/
abbrev NegativeTerm : Type :=
  Negative0.Term ⊕ Negative1.Term ⊕ Negative2.Term ⊕ Negative3.Term ⊕
    Negative4.Term ⊕ Negative5.Term ⊕ Negative6.Term ⊕ Negative7.Term ⊕
    Negative8.Term ⊕ Negative9.Term ⊕ Negative10.Term ⊕ Negative11.Term ⊕
    Negative12.Term ⊕ Negative13.Term ⊕ Negative14.Term ⊕ Negative15.Term

/-- Decidable equality of the global positive index.

Instance search does not reach this on its own: it branches at every summand, so a 17-fold
disjoint union exhausts the default `synthInstance.maxSize` (the limit is already hit at seven
summands).  Building the instance bottom up keeps every step at depth one.  `Fintype` needs no
such help. -/
instance instDecidableEqPositiveTerm : DecidableEq PositiveTerm :=
  @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    inferInstance

/-- Decidable equality of the global negative index, built the same way. -/
instance instDecidableEqNegativeTerm : DecidableEq NegativeTerm :=
  @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <| @instDecidableEqSum _ _ inferInstance <|
    @instDecidableEqSum _ _ inferInstance <|
    inferInstance

/-- Committed odd mantissa of a global positive index, dispatched to its chunk's array. -/
def positiveArgumentNat : PositiveTerm → ℕ :=
  Sum.elim Positive0.argument <| Sum.elim Positive1.argument <|
    Sum.elim Positive2.argument <| Sum.elim Positive3.argument <|
    Sum.elim Positive4.argument <| Sum.elim Positive5.argument <|
    Sum.elim Positive6.argument <| Sum.elim Positive7.argument <|
    Sum.elim Positive8.argument <| Sum.elim Positive9.argument <|
    Sum.elim Positive10.argument <| Sum.elim Positive11.argument <|
    Sum.elim Positive12.argument <| Sum.elim Positive13.argument <|
    Sum.elim Positive14.argument <| Sum.elim Positive15.argument <|
    Positive16.argument

/-- Committed dyadic numerator of a global positive index. -/
def positiveNumerator : PositiveTerm → ℕ :=
  Sum.elim Positive0.coefficient <| Sum.elim Positive1.coefficient <|
    Sum.elim Positive2.coefficient <| Sum.elim Positive3.coefficient <|
    Sum.elim Positive4.coefficient <| Sum.elim Positive5.coefficient <|
    Sum.elim Positive6.coefficient <| Sum.elim Positive7.coefficient <|
    Sum.elim Positive8.coefficient <| Sum.elim Positive9.coefficient <|
    Sum.elim Positive10.coefficient <| Sum.elim Positive11.coefficient <|
    Sum.elim Positive12.coefficient <| Sum.elim Positive13.coefficient <|
    Sum.elim Positive14.coefficient <| Sum.elim Positive15.coefficient <|
    Positive16.coefficient

/-- Committed odd mantissa of a global negative index. -/
def negativeArgumentNat : NegativeTerm → ℕ :=
  Sum.elim Negative0.argument <| Sum.elim Negative1.argument <|
    Sum.elim Negative2.argument <| Sum.elim Negative3.argument <|
    Sum.elim Negative4.argument <| Sum.elim Negative5.argument <|
    Sum.elim Negative6.argument <| Sum.elim Negative7.argument <|
    Sum.elim Negative8.argument <| Sum.elim Negative9.argument <|
    Sum.elim Negative10.argument <| Sum.elim Negative11.argument <|
    Sum.elim Negative12.argument <| Sum.elim Negative13.argument <|
    Sum.elim Negative14.argument <| Negative15.argument

/-- Committed dyadic numerator of a global negative index. -/
def negativeNumerator : NegativeTerm → ℕ :=
  Sum.elim Negative0.coefficient <| Sum.elim Negative1.coefficient <|
    Sum.elim Negative2.coefficient <| Sum.elim Negative3.coefficient <|
    Sum.elim Negative4.coefficient <| Sum.elim Negative5.coefficient <|
    Sum.elim Negative6.coefficient <| Sum.elim Negative7.coefficient <|
    Sum.elim Negative8.coefficient <| Sum.elim Negative9.coefficient <|
    Sum.elim Negative10.coefficient <| Sum.elim Negative11.coefficient <|
    Sum.elim Negative12.coefficient <| Sum.elim Negative13.coefficient <|
    Sum.elim Negative14.coefficient <| Negative15.coefficient

/-- Real weight of one committed positive odd mantissa. -/
def positiveWeight (term : PositiveTerm) : ℝ := mass bits (positiveNumerator term)

/-- Real value of one committed positive odd mantissa. -/
def positiveArgument (term : PositiveTerm) : ℝ := (positiveArgumentNat term : ℝ)

/-- Real weight of one committed negative odd mantissa. -/
def negativeWeight (term : NegativeTerm) : ℝ := mass bits (negativeNumerator term)

/-- Real value of one committed negative odd mantissa. -/
def negativeArgument (term : NegativeTerm) : ℝ := (negativeArgumentNat term : ℝ)

/-! ## Positivity of the committed mantissas

Each chunk proves `arguments_pos` by `decide` on its own array; the global statement is the case
split over the 17 (resp. 16) chunks, and adds no arithmetic.
-/

theorem positiveArgumentNat_pos : ∀ term, 0 < positiveArgumentNat term := by
  rintro (t | t | t | t | t | t | t | t | t | t | t | t | t | t | t | t | t)
  exacts [Positive0.arguments_pos t, Positive1.arguments_pos t, Positive2.arguments_pos t,
    Positive3.arguments_pos t, Positive4.arguments_pos t, Positive5.arguments_pos t,
    Positive6.arguments_pos t, Positive7.arguments_pos t, Positive8.arguments_pos t,
    Positive9.arguments_pos t, Positive10.arguments_pos t, Positive11.arguments_pos t,
    Positive12.arguments_pos t, Positive13.arguments_pos t, Positive14.arguments_pos t,
    Positive15.arguments_pos t, Positive16.arguments_pos t]

theorem negativeArgumentNat_pos : ∀ term, 0 < negativeArgumentNat term := by
  rintro (t | t | t | t | t | t | t | t | t | t | t | t | t | t | t | t)
  exacts [Negative0.arguments_pos t, Negative1.arguments_pos t, Negative2.arguments_pos t,
    Negative3.arguments_pos t, Negative4.arguments_pos t, Negative5.arguments_pos t,
    Negative6.arguments_pos t, Negative7.arguments_pos t, Negative8.arguments_pos t,
    Negative9.arguments_pos t, Negative10.arguments_pos t, Negative11.arguments_pos t,
    Negative12.arguments_pos t, Negative13.arguments_pos t, Negative14.arguments_pos t,
    Negative15.arguments_pos t]

theorem positiveArgument_pos : ∀ term, 0 < positiveArgument term := by
  intro term
  have hpositive := positiveArgumentNat_pos term
  unfold positiveArgument
  exact_mod_cast hpositive

theorem negativeArgument_pos : ∀ term, 0 < negativeArgument term := by
  intro term
  have hnegative := negativeArgumentNat_pos term
  unfold negativeArgument
  exact_mod_cast hnegative

/-! ## The chunked payload as one signed log-linear form -/

/-- **The committed chunk sums are one global sum.**  The positive half of the emitted witness,
`Positive0.exact + … + Positive16.exact`, is the single weighted logarithm sum over the global
mantissa index: the disjoint-union reindexing `Fintype.sum_sum_type` and nothing else. -/
theorem positiveExactSum_eq_sum :
    positiveExactSum =
      ∑ term : PositiveTerm,
        positiveWeight term * (Real.log (positiveArgument term) / Real.log 2) := by
  unfold positiveWeight positiveArgument positiveNumerator positiveArgumentNat
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  unfold positiveExactSum
  simp only [Positive0.exact, Positive1.exact, Positive2.exact, Positive3.exact, Positive4.exact,
    Positive5.exact, Positive6.exact, Positive7.exact, Positive8.exact, Positive9.exact,
    Positive10.exact, Positive11.exact, Positive12.exact, Positive13.exact, Positive14.exact,
    Positive15.exact, Positive16.exact,
    MatrixMultiplication.DyadicLogLinear.logSum, bits]
  ring

/-- The same reindexing on the negative half. -/
theorem negativeExactSum_eq_sum :
    negativeExactSum =
      ∑ term : NegativeTerm,
        negativeWeight term * (Real.log (negativeArgument term) / Real.log 2) := by
  unfold negativeWeight negativeArgument negativeNumerator negativeArgumentNat
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  unfold negativeExactSum
  simp only [Negative0.exact, Negative1.exact, Negative2.exact, Negative3.exact, Negative4.exact,
    Negative5.exact, Negative6.exact, Negative7.exact, Negative8.exact, Negative9.exact,
    Negative10.exact, Negative11.exact, Negative12.exact, Negative13.exact, Negative14.exact,
    Negative15.exact,
    MatrixMultiplication.DyadicLogLinear.logSum, bits]
  ring

/-- **The committed payload is a signed log-linear form.**  The generated modules store a dyadic
constant, one nonnegative coefficient per committed odd mantissa on each side, and a single
residual coefficient of `1 / log 2`; the witness is the exact value of that form plus the residual
term.

Definitional once the two chunk reindexings are in hand, and it is what lets the emitter identity
below be stated entirely inside the generic compression vocabulary. -/
theorem retainedExponentLowerWitness_eq_exactValue :
    retainedExponentLowerWitness =
      exactValue (mass bits constantNumerator) positiveWeight positiveArgument
          negativeWeight negativeArgument +
        inverseLogTerm := by
  unfold retainedExponentLowerWitness exactValue
  rw [positiveExactSum_eq_sum, negativeExactSum_eq_sum]

/-! ## Half one of the seam, with the emitter identity discharged -/

/-- **The deliverable.**  The exporter's last step regroups the chord expansion onto odd mantissas
(`normalize_power_of_two_factors`).  By `chordTangentValue_eq_normalized` that regrouping is an
exact identity, so the `hwitness` inequality of
`TotalQuotientRetainedCompressionSeam.retainedCompressionSeam_of_chordTangentCompression` becomes
four finite statements about the emitted arrays — no logarithm, no re-indexing, no analysis:

* `hendpointFactor`, `hcenterFactor` — each bin endpoint and each bin centre is `2 ^ k` times one
  of the committed odd mantissas (a `decide` on ℕ arrays; the exporter emits the endpoints already
  factored, so no `Nat.log` is evaluated in the kernel);
* `hconstant` — the committed dyadic constant is the form's constant plus the two valuation
  shifts;
* `hpositiveCoefficient`, `hnegativeCoefficient` — each committed coefficient is the fiber sum of
  the chord/pooling coefficients landing on that mantissa (`positiveWeight_eq_of_chunks` below
  assembles these two chunk by chunk);
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
    (endpointValuation : Bin ⊕ Bin → ℕ) (endpointMantissa : Bin ⊕ Bin → PositiveTerm)
    (centerValuation : BinNeg → ℕ) (centerMantissa : BinNeg → NegativeTerm)
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

/-! ## The rational entry point

`LogLinearRationalAccumulation.lean` proves that every ingredient of the four hypotheses above is
the cast of a `ℚ`-valued computation.  The committed dyadic constant is the one remaining
ingredient, and it is a rational cast too.
-/

/-- The committed dyadic mass as an explicit rational cast: a numerator over `2 ^ bits` enters a
`ℚ`-level statement without a real division. -/
theorem mass_eq_ratCast (numerator : ℕ) :
    mass bits numerator = (((numerator : ℚ) / (2 : ℚ) ^ bits : ℚ) : ℝ) := by
  simp only [mass, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]

/-- **The seam from `ℚ`-valued emitter data.**  Same statement as
`retainedCompressionSeam_of_normalizedChordTangentCompression`, with the emitted item weights,
arguments, bin endpoints and centres *rational* and every hypothesis except `hsemantic` a
statement of `ℚ`: the four emitter identities, the bracketing inequalities and the sign
conditions.  So the whole compression obligation of this certificate is decidable rational
arithmetic — no real number, no logarithm, and (by `LogLinearCompression.fiberSumIn_div` and
`fiberSumIn_intCast`) reducible further to integer sums over the fixed denominator
`2 ^ (bits + maxShift)`, which is what a chunked kernel accumulation can produce.

`hresidual` keeps the committed `inverseLogCoefficient` on its left, since the generated module
commits that one coefficient as a real literal; everything on its right is rational. -/
theorem retainedCompressionSeam_of_rationalNormalizedChordTangentCompression
    {Item ItemNeg : Type u} {Bin BinNeg : Type v}
    [Fintype Item] [Fintype ItemNeg] [Fintype Bin] [Fintype BinNeg]
    [DecidableEq Bin] [DecidableEq BinNeg]
    {semanticRetained : ℝ}
    (constant : ℚ)
    (positiveBin : Item → Bin) (positiveItemWeight positiveItemArgument : Item → ℚ)
    (lower upper : Bin → ℚ)
    (negativeBin : ItemNeg → BinNeg) (negativeItemWeight negativeItemArgument : ItemNeg → ℚ)
    (center : BinNeg → ℚ)
    (endpointValuation : Bin ⊕ Bin → ℕ) (endpointMantissa : Bin ⊕ Bin → PositiveTerm)
    (centerValuation : BinNeg → ℕ) (centerMantissa : BinNeg → NegativeTerm)
    (hendpointFactor : ∀ x, Sum.elim lower upper x =
      (2 : ℚ) ^ endpointValuation x * (positiveArgumentNat (endpointMantissa x) : ℚ))
    (hcenterFactor : ∀ b, center b =
      (2 : ℚ) ^ centerValuation b * (negativeArgumentNat (centerMantissa b) : ℚ))
    (hconstant : (constantNumerator : ℚ) / (2 : ℚ) ^ bits =
      constant +
          valuationShiftIn
            (Sum.elim
              (chordLowerCoefficientIn positiveBin positiveItemWeight positiveItemArgument
                lower upper)
              (chordUpperCoefficientIn positiveBin positiveItemWeight positiveItemArgument
                lower upper))
            endpointValuation -
        valuationShiftIn (fiberSumIn negativeBin negativeItemWeight) centerValuation)
    (hpositiveCoefficient : ∀ m, (positiveNumerator m : ℚ) / (2 : ℚ) ^ bits =
      fiberSumIn endpointMantissa
        (Sum.elim
          (chordLowerCoefficientIn positiveBin positiveItemWeight positiveItemArgument
            lower upper)
          (chordUpperCoefficientIn positiveBin positiveItemWeight positiveItemArgument
            lower upper)) m)
    (hnegativeCoefficient : ∀ m, (negativeNumerator m : ℚ) / (2 : ℚ) ^ bits =
      fiberSumIn centerMantissa (fiberSumIn negativeBin negativeItemWeight) m)
    (hresidual : inverseLogCoefficient =
      ((tangentResidualIn negativeBin negativeItemWeight negativeItemArgument center : ℚ) : ℝ))
    (hpositiveWeight : ∀ item, 0 ≤ positiveItemWeight item)
    (hlower : ∀ b, 0 < lower b)
    (hlowerLe : ∀ item, lower (positiveBin item) ≤ positiveItemArgument item)
    (hleUpper : ∀ item, positiveItemArgument item ≤ upper (positiveBin item))
    (hlowerLtUpper : ∀ b, lower b < upper b)
    (hnegativeWeight : ∀ item, 0 ≤ negativeItemWeight item)
    (hnegativeArgument : ∀ item, 0 < negativeItemArgument item)
    (hcenter : ∀ b, 0 < center b)
    (hsemantic :
      exactValue (constant : ℝ) (fun item ↦ ((positiveItemWeight item : ℚ) : ℝ))
          (fun item ↦ ((positiveItemArgument item : ℚ) : ℝ))
          (fun item ↦ ((negativeItemWeight item : ℚ) : ℝ))
          (fun item ↦ ((negativeItemArgument item : ℚ) : ℝ)) ≤
        semanticRetained) :
    RetainedCompressionSeam semanticRetained := by
  have helim : ∀ x, Sum.elim (fun b ↦ ((lower b : ℚ) : ℝ)) (fun b ↦ ((upper b : ℚ) : ℝ)) x =
      ((Sum.elim lower upper x : ℚ) : ℝ) := by
    intro x
    cases x <;> rfl
  have hchordFamily :
      Sum.elim
          (chordLowerCoefficient positiveBin (fun item ↦ ((positiveItemWeight item : ℚ) : ℝ))
            (fun item ↦ ((positiveItemArgument item : ℚ) : ℝ))
            (fun b ↦ ((lower b : ℚ) : ℝ)) (fun b ↦ ((upper b : ℚ) : ℝ)))
          (chordUpperCoefficient positiveBin (fun item ↦ ((positiveItemWeight item : ℚ) : ℝ))
            (fun item ↦ ((positiveItemArgument item : ℚ) : ℝ))
            (fun b ↦ ((lower b : ℚ) : ℝ)) (fun b ↦ ((upper b : ℚ) : ℝ))) =
        fun x ↦ ((Sum.elim
          (chordLowerCoefficientIn positiveBin positiveItemWeight positiveItemArgument
            lower upper)
          (chordUpperCoefficientIn positiveBin positiveItemWeight positiveItemArgument
            lower upper) x : ℚ) : ℝ) := by
    funext x
    cases x with
    | inl b =>
        exact chordLowerCoefficient_ratCast positiveBin positiveItemWeight positiveItemArgument
          lower upper b
    | inr b =>
        exact chordUpperCoefficient_ratCast positiveBin positiveItemWeight positiveItemArgument
          lower upper b
  have hpooled : fiberSum negativeBin (fun item ↦ ((negativeItemWeight item : ℚ) : ℝ)) =
      fun b ↦ ((fiberSumIn negativeBin negativeItemWeight b : ℚ) : ℝ) := by
    funext b
    exact fiberSum_ratCast negativeBin negativeItemWeight b
  refine retainedCompressionSeam_of_normalizedChordTangentCompression ((constant : ℚ) : ℝ)
    positiveBin (fun item ↦ ((positiveItemWeight item : ℚ) : ℝ))
    (fun item ↦ ((positiveItemArgument item : ℚ) : ℝ))
    (fun b ↦ ((lower b : ℚ) : ℝ)) (fun b ↦ ((upper b : ℚ) : ℝ)) negativeBin
    (fun item ↦ ((negativeItemWeight item : ℚ) : ℝ))
    (fun item ↦ ((negativeItemArgument item : ℚ) : ℝ)) (fun b ↦ ((center b : ℚ) : ℝ))
    endpointValuation endpointMantissa centerValuation centerMantissa
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsemantic
  · intro x
    rw [helim x, hendpointFactor x]
    unfold positiveArgument
    push_cast
    ring
  · intro b
    rw [hcenterFactor b]
    unfold negativeArgument
    push_cast
    ring
  · rw [mass_eq_ratCast, hconstant, hchordFamily, hpooled, valuationShift_ratCast,
      valuationShift_ratCast]
    push_cast
    ring
  · funext m
    unfold positiveWeight
    rw [mass_eq_ratCast, hpositiveCoefficient m, hchordFamily, fiberSum_ratCast]
  · funext m
    unfold negativeWeight
    rw [mass_eq_ratCast, hnegativeCoefficient m, hpooled, fiberSum_ratCast]
  · rw [hresidual, tangentResidual_ratCast]
  · intro item
    exact_mod_cast hpositiveWeight item
  · intro b
    exact_mod_cast hlower b
  · intro item
    exact_mod_cast hlowerLe item
  · intro item
    exact_mod_cast hleUpper item
  · intro b
    exact_mod_cast hlowerLtUpper b
  · intro item
    exact_mod_cast hnegativeWeight item
  · intro item
    exact_mod_cast hnegativeArgument item
  · intro b
    exact_mod_cast hcenter b

/-! ## The chunked-accumulation skeleton

The two coefficient-family hypotheses above are equalities of *functions* on the global mantissa
index.  Because that index is the disjoint union of the committed chunks, such an equality is
exactly one fact per chunk — 17 on the positive side, 16 on the negative — and each of those is a
statement about a single committed array of at most 64 mantissas.  The two theorems below are that
assembly, with the per-chunk facts as named hypotheses, so a future per-chunk integral
accumulation can be plugged in without restating the seam.  They are parameterized over an
arbitrary target family `expected`; at the call site it is the fiber sum of the chord
coefficients.

The chunk embeddings name the summands of the global index.
-/

def positiveChunk0 : Positive0.Term → PositiveTerm := Sum.inl
def positiveChunk1 : Positive1.Term → PositiveTerm := Sum.inr ∘ Sum.inl
def positiveChunk2 : Positive2.Term → PositiveTerm := Sum.inr ∘ Sum.inr ∘ Sum.inl
def positiveChunk3 : Positive3.Term → PositiveTerm := Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def positiveChunk4 : Positive4.Term → PositiveTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def positiveChunk5 : Positive5.Term → PositiveTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def positiveChunk6 : Positive6.Term → PositiveTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def positiveChunk7 : Positive7.Term → PositiveTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def positiveChunk8 : Positive8.Term → PositiveTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inl
def positiveChunk9 : Positive9.Term → PositiveTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inl
def positiveChunk10 : Positive10.Term → PositiveTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inr ∘ Sum.inl
def positiveChunk11 : Positive11.Term → PositiveTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def positiveChunk12 : Positive12.Term → PositiveTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def positiveChunk13 : Positive13.Term → PositiveTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def positiveChunk14 : Positive14.Term → PositiveTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def positiveChunk15 : Positive15.Term → PositiveTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def positiveChunk16 : Positive16.Term → PositiveTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr

def negativeChunk0 : Negative0.Term → NegativeTerm := Sum.inl
def negativeChunk1 : Negative1.Term → NegativeTerm := Sum.inr ∘ Sum.inl
def negativeChunk2 : Negative2.Term → NegativeTerm := Sum.inr ∘ Sum.inr ∘ Sum.inl
def negativeChunk3 : Negative3.Term → NegativeTerm := Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def negativeChunk4 : Negative4.Term → NegativeTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def negativeChunk5 : Negative5.Term → NegativeTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def negativeChunk6 : Negative6.Term → NegativeTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def negativeChunk7 : Negative7.Term → NegativeTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def negativeChunk8 : Negative8.Term → NegativeTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inl
def negativeChunk9 : Negative9.Term → NegativeTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inl
def negativeChunk10 : Negative10.Term → NegativeTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inr ∘ Sum.inl
def negativeChunk11 : Negative11.Term → NegativeTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def negativeChunk12 : Negative12.Term → NegativeTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def negativeChunk13 : Negative13.Term → NegativeTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def negativeChunk14 : Negative14.Term → NegativeTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl
def negativeChunk15 : Negative15.Term → NegativeTerm :=
  Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘
    Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr

/-- **Chunked assembly of the positive coefficient identity.**  The identity the seam
asks for is an equality of families on the global index, so it amounts to exactly one fact per
committed chunk (seventeen of them), each about a single array of at most 64 mantissas. -/
theorem positiveWeight_eq_of_chunks {expected : PositiveTerm → ℝ}
    (h0 : ∀ t, mass bits (Positive0.coefficient t) = expected (positiveChunk0 t))
    (h1 : ∀ t, mass bits (Positive1.coefficient t) = expected (positiveChunk1 t))
    (h2 : ∀ t, mass bits (Positive2.coefficient t) = expected (positiveChunk2 t))
    (h3 : ∀ t, mass bits (Positive3.coefficient t) = expected (positiveChunk3 t))
    (h4 : ∀ t, mass bits (Positive4.coefficient t) = expected (positiveChunk4 t))
    (h5 : ∀ t, mass bits (Positive5.coefficient t) = expected (positiveChunk5 t))
    (h6 : ∀ t, mass bits (Positive6.coefficient t) = expected (positiveChunk6 t))
    (h7 : ∀ t, mass bits (Positive7.coefficient t) = expected (positiveChunk7 t))
    (h8 : ∀ t, mass bits (Positive8.coefficient t) = expected (positiveChunk8 t))
    (h9 : ∀ t, mass bits (Positive9.coefficient t) = expected (positiveChunk9 t))
    (h10 : ∀ t, mass bits (Positive10.coefficient t) = expected (positiveChunk10 t))
    (h11 : ∀ t, mass bits (Positive11.coefficient t) = expected (positiveChunk11 t))
    (h12 : ∀ t, mass bits (Positive12.coefficient t) = expected (positiveChunk12 t))
    (h13 : ∀ t, mass bits (Positive13.coefficient t) = expected (positiveChunk13 t))
    (h14 : ∀ t, mass bits (Positive14.coefficient t) = expected (positiveChunk14 t))
    (h15 : ∀ t, mass bits (Positive15.coefficient t) = expected (positiveChunk15 t))
    (h16 : ∀ t, mass bits (Positive16.coefficient t) = expected (positiveChunk16 t))
    : positiveWeight = expected := by
  funext term
  rcases term with t | t | t | t | t | t | t | t | t | t | t | t | t | t | t | t | t
  exacts [h0 t, h1 t, h2 t, h3 t, h4 t, h5 t,
    h6 t, h7 t, h8 t, h9 t, h10 t, h11 t,
    h12 t, h13 t, h14 t, h15 t, h16 t]

/-- **Chunked assembly of the negative coefficient identity.**  The identity the seam
asks for is an equality of families on the global index, so it amounts to exactly one fact per
committed chunk (sixteen of them), each about a single array of at most 64 mantissas. -/
theorem negativeWeight_eq_of_chunks {expected : NegativeTerm → ℝ}
    (h0 : ∀ t, mass bits (Negative0.coefficient t) = expected (negativeChunk0 t))
    (h1 : ∀ t, mass bits (Negative1.coefficient t) = expected (negativeChunk1 t))
    (h2 : ∀ t, mass bits (Negative2.coefficient t) = expected (negativeChunk2 t))
    (h3 : ∀ t, mass bits (Negative3.coefficient t) = expected (negativeChunk3 t))
    (h4 : ∀ t, mass bits (Negative4.coefficient t) = expected (negativeChunk4 t))
    (h5 : ∀ t, mass bits (Negative5.coefficient t) = expected (negativeChunk5 t))
    (h6 : ∀ t, mass bits (Negative6.coefficient t) = expected (negativeChunk6 t))
    (h7 : ∀ t, mass bits (Negative7.coefficient t) = expected (negativeChunk7 t))
    (h8 : ∀ t, mass bits (Negative8.coefficient t) = expected (negativeChunk8 t))
    (h9 : ∀ t, mass bits (Negative9.coefficient t) = expected (negativeChunk9 t))
    (h10 : ∀ t, mass bits (Negative10.coefficient t) = expected (negativeChunk10 t))
    (h11 : ∀ t, mass bits (Negative11.coefficient t) = expected (negativeChunk11 t))
    (h12 : ∀ t, mass bits (Negative12.coefficient t) = expected (negativeChunk12 t))
    (h13 : ∀ t, mass bits (Negative13.coefficient t) = expected (negativeChunk13 t))
    (h14 : ∀ t, mass bits (Negative14.coefficient t) = expected (negativeChunk14 t))
    (h15 : ∀ t, mass bits (Negative15.coefficient t) = expected (negativeChunk15 t))
    : negativeWeight = expected := by
  funext term
  rcases term with t | t | t | t | t | t | t | t | t | t | t | t | t | t | t | t
  exacts [h0 t, h1 t, h2 t, h3 t, h4 t, h5 t,
    h6 t, h7 t, h8 t, h9 t, h10 t, h11 t,
    h12 t, h13 t, h14 t, h15 t]

end

end MatrixMultiplication.TotalQuotientNormalizedCompression
