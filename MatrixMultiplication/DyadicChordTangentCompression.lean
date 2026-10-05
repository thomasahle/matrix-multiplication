/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.LogLinearCompressionFamily

/-!
# Chord/tangent compression of a signed log-linear form at an arbitrary mantissa width

`LogLinearCompression.lean` proves the two scalar inequalities — a logarithm lies above the chord
through two positive endpoints, and below the tangent at any positive centre — and
`LogLinearCompressionFamily.lean` lifts them to a finite family binned by an arbitrary map.  This
module supplies the two pieces that turn those inequalities into the *exact* compression the
certificate exporter performs, and proves that the exporter's runtime assertion
`compressed ≤ exact` is a theorem.

## What the exporter does

For a signed log-linear form `c + Σᵢ pᵢ log₂ aᵢ − Σⱼ nⱼ log₂ bⱼ` with positive integer arguments
and a chosen mantissa width `m`, each argument `a` is placed in the dyadic bin of width
`2 ^ (⌊log₂ a⌋ − m)` containing it:

* a **positive** coefficient is replaced by the two chord coefficients at the bin endpoints —
  a lower bound, because `log` is concave;
* the **negative** coefficients of one bin are pooled at the fixed dyadic bin *midpoint* and
  bounded by the tangent there — an upper bound on the subtracted sum, hence again a lower bound
  on the form;
* every first-order tangent error is collected into a single signed rational multiple of
  `1 / log 2`, evaluated with a directed enclosure of `log 2` whose direction depends on the sign
  of that one coefficient.

Using a *fixed* midpoint rather than the exact coefficient-weighted mean is what makes the
compression useful: every surviving logarithm has one of only `2 ^ m` mantissas, so a certificate
with tens of thousands of distinct arguments collapses to a few hundred.  The price is the single
residual term, and `inverseLogTwoFloor` is the directed rational endpoint that discharges it.

## Contents

* `binShift`, `binWidth`, `binLower`, `binUpper`, `binCenter` — the mantissa-`m` dyadic bin of a
  positive integer, and its arithmetic: the endpoints are positive, they bracket the argument
  strictly on the right, and the centre is the exact midpoint whenever the bin is nondegenerate.
* `logTwo_chord_lower_ofMantissa`, `logTwo_le_tangent_ofMantissa` — the two directed inequalities
  at an arbitrary mantissa width, with exact rational endpoints.
* `logTwo_two_pow_mul` — the exact identity `log₂ (2 ^ k a) = k + log₂ a` behind the exporter's
  power-of-two normalization, which moves `k · coefficient` into the constant term.
* `exactValue`, `chordTangentValue`, `chordTangentRationalValue` and the composition theorems
  `chordTangentValue_le_exactValue`, `chordTangentRationalValue_le_exactValue`.
* `le_of_chordTangentCompression` — the form a certificate client consumes: a witness at most the
  compressed value is at most any semantic quantity that dominates the exact value.

## Position in the library

Paper layer (`MatrixMultiplication/`), beside the two modules whose inequalities it composes.  No
declaration here mentions a tensor, an exponent, or a certificate; the arithmetic is stated for an
arbitrary finite family, an arbitrary binning map, and an arbitrary mantissa width.  A generated
client instantiates `Bin` by the finitely many bins its data actually uses and discharges the
bracketing hypotheses by `decide` on the emitted arrays.
-/

open scoped BigOperators

namespace MatrixMultiplication.LogLinearCompression

universe u v

/-! ## Dyadic bins at an arbitrary mantissa width -/

/-- Number of low bits the mantissa-`mantissaBits` compressor discards from `argument`.

Truncated subtraction is exactly the exporter's `max(0, ⌊log₂ a⌋ − m)`: an argument that already
fits in `mantissaBits` bits is left alone. -/
def binShift (mantissaBits argument : ℕ) : ℕ := Nat.log 2 argument - mantissaBits

/-- Width of the dyadic bin of `argument` at mantissa width `mantissaBits`. -/
def binWidth (mantissaBits argument : ℕ) : ℕ := 2 ^ binShift mantissaBits argument

/-- Lower endpoint of the dyadic bin: `argument` with its low `binShift` bits cleared. -/
def binLower (mantissaBits argument : ℕ) : ℕ :=
  argument / binWidth mantissaBits argument * binWidth mantissaBits argument

/-- Upper endpoint of the dyadic bin. -/
def binUpper (mantissaBits argument : ℕ) : ℕ :=
  binLower mantissaBits argument + binWidth mantissaBits argument

/-- Fixed dyadic bin centre, `(lower + upper) / 2` in exact integer arithmetic.

For a nondegenerate bin this is the exact midpoint (`two_mul_binCenter`).  For a degenerate bin —
one whose argument already fits in `mantissaBits` bits — the width is `1`, the centre is the
argument itself, and the tangent bound below is an equality. -/
def binCenter (mantissaBits argument : ℕ) : ℕ :=
  binLower mantissaBits argument + binWidth mantissaBits argument / 2

theorem binWidth_pos (mantissaBits argument : ℕ) : 0 < binWidth mantissaBits argument :=
  pow_pos (by norm_num) _

/-- The bin is never wider than the argument it contains. -/
theorem binWidth_le (mantissaBits : ℕ) {argument : ℕ} (hargument : 0 < argument) :
    binWidth mantissaBits argument ≤ argument := by
  calc binWidth mantissaBits argument ≤ 2 ^ Nat.log 2 argument :=
        Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    _ ≤ argument := Nat.pow_log_le_self 2 hargument.ne'

theorem binLower_le (mantissaBits argument : ℕ) :
    binLower mantissaBits argument ≤ argument :=
  Nat.div_mul_le_self _ _

theorem lt_binUpper (mantissaBits argument : ℕ) :
    argument < binUpper mantissaBits argument := by
  have hwidth := binWidth_pos mantissaBits argument
  have hmod : argument % binWidth mantissaBits argument < binWidth mantissaBits argument :=
    Nat.mod_lt _ hwidth
  calc argument
      = binWidth mantissaBits argument * (argument / binWidth mantissaBits argument) +
          argument % binWidth mantissaBits argument :=
        (Nat.div_add_mod _ _).symm
    _ < binWidth mantissaBits argument * (argument / binWidth mantissaBits argument) +
          binWidth mantissaBits argument := add_lt_add_of_le_of_lt (le_refl _) hmod
    _ = binUpper mantissaBits argument := by
        unfold binUpper binLower
        ring

theorem binLower_pos (mantissaBits : ℕ) {argument : ℕ} (hargument : 0 < argument) :
    0 < binLower mantissaBits argument :=
  Nat.mul_pos
    (Nat.div_pos (binWidth_le mantissaBits hargument) (binWidth_pos mantissaBits argument))
    (binWidth_pos mantissaBits argument)

theorem binLower_lt_binUpper (mantissaBits argument : ℕ) :
    binLower mantissaBits argument < binUpper mantissaBits argument :=
  lt_add_of_pos_right _ (binWidth_pos mantissaBits argument)

theorem binCenter_pos (mantissaBits : ℕ) {argument : ℕ} (hargument : 0 < argument) :
    0 < binCenter mantissaBits argument :=
  lt_of_lt_of_le (binLower_pos mantissaBits hargument) (Nat.le_add_right _ _)

/-- On a nondegenerate bin the integer centre is the exact midpoint of the two endpoints, so the
tangent point is a dyadic rational of the same mantissa width as the endpoints. -/
theorem two_mul_binCenter (mantissaBits argument : ℕ)
    (hshift : 0 < binShift mantissaBits argument) :
    2 * binCenter mantissaBits argument =
      binLower mantissaBits argument + binUpper mantissaBits argument := by
  obtain ⟨half, hhalf⟩ :
      ∃ half, binWidth mantissaBits argument = 2 * half := by
    refine ⟨2 ^ (binShift mantissaBits argument - 1), ?_⟩
    unfold binWidth
    conv_lhs => rw [← Nat.sub_add_cancel hshift]
    rw [pow_succ]
    ring
  unfold binCenter binUpper
  rw [hhalf]
  omega

noncomputable section

/-! ## The two directed inequalities at an arbitrary mantissa width -/

/-- **Chord lower bound at mantissa width `mantissaBits`.**  The chord through the two exact
integer bin endpoints, evaluated at the argument, never exceeds the logarithm: this is concavity,
and it is the inequality that makes the compression of a *positive* log coefficient conservative.

Both endpoints and both chord weights are exact rationals determined by `mantissaBits` and the
argument alone. -/
theorem logTwo_chord_lower_ofMantissa (mantissaBits : ℕ) {argument : ℕ}
    (hargument : 0 < argument) :
    (((binUpper mantissaBits argument : ℝ) - argument) /
          ((binUpper mantissaBits argument : ℝ) - (binLower mantissaBits argument : ℝ))) *
        (Real.log (binLower mantissaBits argument) / Real.log 2) +
      (((argument : ℝ) - (binLower mantissaBits argument : ℝ)) /
          ((binUpper mantissaBits argument : ℝ) - (binLower mantissaBits argument : ℝ))) *
        (Real.log (binUpper mantissaBits argument) / Real.log 2) ≤
      Real.log argument / Real.log 2 := by
  refine logTwo_chord_lower ?_ ?_ ?_ ?_
  · exact_mod_cast binLower_pos mantissaBits hargument
  · exact_mod_cast binLower_le mantissaBits argument
  · exact_mod_cast (lt_binUpper mantissaBits argument).le
  · exact_mod_cast binLower_lt_binUpper mantissaBits argument

/-- **Tangent upper bound at mantissa width `mantissaBits`.**  The tangent to `log₂` at the fixed
dyadic bin centre dominates the logarithm everywhere, so pooling the *negative* log coefficients
of a bin at that centre and paying the exact first-order rational error is conservative. -/
theorem logTwo_le_tangent_ofMantissa (mantissaBits : ℕ) {argument : ℕ}
    (hargument : 0 < argument) :
    Real.log argument / Real.log 2 ≤
      Real.log (binCenter mantissaBits argument) / Real.log 2 +
        (((argument : ℝ) - (binCenter mantissaBits argument : ℝ)) /
          (binCenter mantissaBits argument : ℝ)) / Real.log 2 := by
  refine logTwo_tangent_upper ?_ ?_
  · exact_mod_cast hargument
  · exact_mod_cast binCenter_pos mantissaBits hargument

/-- **Exact power-of-two normalization.**  `log₂ (2 ^ k a) = k + log₂ a`, the identity the
exporter uses to collapse every dyadic-grid argument onto its odd mantissa and move the discarded
`k · coefficient` into the constant term.  It is an equality, so it costs no slack. -/
theorem logTwo_two_pow_mul (k : ℕ) {argument : ℝ} (hargument : 0 < argument) :
    Real.log ((2 : ℝ) ^ k * argument) / Real.log 2 =
      (k : ℝ) + Real.log argument / Real.log 2 := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [Real.log_mul (by positivity) hargument.ne', Real.log_pow]
  field_simp

/-! ## The signed composition -/

variable {Item ItemNeg : Type u} {Bin BinNeg : Type v}

/-- Exact value of a signed log-linear form: a constant, a nonnegatively weighted sum of base-two
logarithms, and a nonnegatively weighted sum that is subtracted. -/
def exactValue [Fintype Item] [Fintype ItemNeg]
    (constant : ℝ) (positiveWeight positiveArgument : Item → ℝ)
    (negativeWeight negativeArgument : ItemNeg → ℝ) : ℝ :=
  constant + (∑ item, positiveWeight item * (Real.log (positiveArgument item) / Real.log 2)) -
    ∑ item, negativeWeight item * (Real.log (negativeArgument item) / Real.log 2)

/-- The single signed first-order remainder produced by pooling the negative coefficients at the
fixed bin centres.  It is an exact rational whenever the weights, arguments and centres are, and
the compressed form carries it as one coefficient of `1 / log 2`. -/
def tangentResidual [Fintype ItemNeg]
    (negativeBin : ItemNeg → BinNeg) (negativeWeight negativeArgument : ItemNeg → ℝ)
    (center : BinNeg → ℝ) : ℝ :=
  -∑ item, negativeWeight item * (negativeArgument item / center (negativeBin item) - 1)

/-- Everything in the compressed form except the residual: the constant, the two chord endpoint
sums per positive bin, and the pooled centre logarithm per negative bin. -/
def chordTangentCore [Fintype Item] [Fintype ItemNeg] [Fintype Bin] [Fintype BinNeg]
    [DecidableEq Bin] [DecidableEq BinNeg]
    (constant : ℝ)
    (positiveBin : Item → Bin) (positiveWeight positiveArgument : Item → ℝ)
    (lower upper : Bin → ℝ)
    (negativeBin : ItemNeg → BinNeg) (negativeWeight : ItemNeg → ℝ)
    (center : BinNeg → ℝ) : ℝ :=
  constant +
      (∑ b : Bin,
        (chordLowerCoefficient positiveBin positiveWeight positiveArgument lower upper b *
            (Real.log (lower b) / Real.log 2) +
          chordUpperCoefficient positiveBin positiveWeight positiveArgument lower upper b *
            (Real.log (upper b) / Real.log 2))) -
    ∑ b : BinNeg, fiberSum negativeBin negativeWeight b * (Real.log (center b) / Real.log 2)

/-- Value of the compressed form, with the residual evaluated against the true `log 2`. -/
def chordTangentValue [Fintype Item] [Fintype ItemNeg] [Fintype Bin] [Fintype BinNeg]
    [DecidableEq Bin] [DecidableEq BinNeg]
    (constant : ℝ)
    (positiveBin : Item → Bin) (positiveWeight positiveArgument : Item → ℝ)
    (lower upper : Bin → ℝ)
    (negativeBin : ItemNeg → BinNeg) (negativeWeight negativeArgument : ItemNeg → ℝ)
    (center : BinNeg → ℝ) : ℝ :=
  chordTangentCore constant positiveBin positiveWeight positiveArgument lower upper
      negativeBin negativeWeight center +
    tangentResidual negativeBin negativeWeight negativeArgument center / Real.log 2

/-- **The composition theorem.**  The chord/tangent compression of a signed log-linear form is a
lower bound for it, at any binning and hence at any mantissa width.

This is exactly the exporter's runtime assertion `compressed ≤ exact`, discharged as a theorem:
the positive half is concavity, the negative half is the tangent bound, and the two first-order
error sums meet in the single residual coefficient of `1 / log 2`. -/
theorem chordTangentValue_le_exactValue
    [Fintype Item] [Fintype ItemNeg] [Fintype Bin] [Fintype BinNeg]
    [DecidableEq Bin] [DecidableEq BinNeg]
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
    (hcenter : ∀ b, 0 < center b) :
    chordTangentValue constant positiveBin positiveWeight positiveArgument lower upper
        negativeBin negativeWeight negativeArgument center ≤
      exactValue constant positiveWeight positiveArgument negativeWeight negativeArgument := by
  have hchord := binned_weighted_logTwo_chord_lower positiveBin positiveWeight positiveArgument
    lower upper hpositiveWeight hlower hlowerLe hleUpper hlowerLtUpper
  have htangent := neg_binned_weighted_logTwo_tangent_lower negativeBin negativeWeight
    negativeArgument center hnegativeWeight hnegativeArgument hcenter
  have hresidual :
      tangentResidual negativeBin negativeWeight negativeArgument center / Real.log 2 =
        -((∑ item, negativeWeight item *
            (negativeArgument item / center (negativeBin item) - 1)) / Real.log 2) := by
    unfold tangentResidual
    rw [neg_div]
  unfold chordTangentValue chordTangentCore exactValue
  rw [hresidual]
  linarith

/-! ## Directed evaluation of the residual

The residual coefficient is signed, so a fully rational endpoint must pick the direction of the
`log 2` enclosure by its sign: a nonnegative coefficient is divided by an upper enclosure, a
negative one by a lower enclosure.  This is the generic form of the two-branch proof the exporter
emits for each certificate.
-/

/-- Directed rational endpoint for a signed multiple of `1 / log 2`. -/
def inverseLogTwoFloor (residual logTwoLower logTwoUpper : ℝ) : ℝ :=
  if 0 ≤ residual then residual / logTwoUpper else residual / logTwoLower

/-- A nonnegative residual is divided by the *upper* enclosure of `log 2`. -/
theorem inverseLogTwoFloor_of_nonneg {residual : ℝ} (hresidual : 0 ≤ residual)
    (logTwoLower logTwoUpper : ℝ) :
    inverseLogTwoFloor residual logTwoLower logTwoUpper = residual / logTwoUpper :=
  if_pos hresidual

/-- A negative residual is divided by the *lower* enclosure of `log 2`. -/
theorem inverseLogTwoFloor_of_neg {residual : ℝ} (hresidual : residual < 0)
    (logTwoLower logTwoUpper : ℝ) :
    inverseLogTwoFloor residual logTwoLower logTwoUpper = residual / logTwoLower :=
  if_neg (not_le.mpr hresidual)

/-- The directed endpoint is a genuine lower bound for the residual term, whichever sign the
residual coefficient has. -/
theorem inverseLogTwoFloor_le {residual logTwoLower logTwoUpper : ℝ}
    (hlowerPos : 0 < logTwoLower) (hlower : logTwoLower ≤ Real.log 2)
    (hupper : Real.log 2 ≤ logTwoUpper) :
    inverseLogTwoFloor residual logTwoLower logTwoUpper ≤ residual / Real.log 2 := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold inverseLogTwoFloor
  split_ifs with hsign
  · exact div_le_div_of_nonneg_left hsign hlogTwo hupper
  · have hnegative : residual < 0 := not_le.mp hsign
    have hnonneg : 0 ≤ -residual := by linarith
    have hstep := div_le_div_of_nonneg_left hnonneg hlowerPos hlower
    simpa only [neg_div, neg_neg] using neg_le_neg hstep

/-- Value of the compressed form with the residual evaluated at directed rational enclosures of
`log 2`.  Every ingredient is an exact rational once the weights, arguments, endpoints, centres
and the two enclosures are. -/
def chordTangentRationalValue [Fintype Item] [Fintype ItemNeg] [Fintype Bin] [Fintype BinNeg]
    [DecidableEq Bin] [DecidableEq BinNeg]
    (constant : ℝ)
    (positiveBin : Item → Bin) (positiveWeight positiveArgument : Item → ℝ)
    (lower upper : Bin → ℝ)
    (negativeBin : ItemNeg → BinNeg) (negativeWeight negativeArgument : ItemNeg → ℝ)
    (center : BinNeg → ℝ) (logTwoLower logTwoUpper : ℝ) : ℝ :=
  chordTangentCore constant positiveBin positiveWeight positiveArgument lower upper
      negativeBin negativeWeight center +
    inverseLogTwoFloor (tangentResidual negativeBin negativeWeight negativeArgument center)
      logTwoLower logTwoUpper

/-- The fully rational compressed endpoint is a lower bound for the exact value of the form. -/
theorem chordTangentRationalValue_le_exactValue
    [Fintype Item] [Fintype ItemNeg] [Fintype Bin] [Fintype BinNeg]
    [DecidableEq Bin] [DecidableEq BinNeg]
    (constant : ℝ)
    (positiveBin : Item → Bin) (positiveWeight positiveArgument : Item → ℝ)
    (lower upper : Bin → ℝ)
    (negativeBin : ItemNeg → BinNeg) (negativeWeight negativeArgument : ItemNeg → ℝ)
    (center : BinNeg → ℝ) {logTwoLower logTwoUpper : ℝ}
    (hpositiveWeight : ∀ item, 0 ≤ positiveWeight item)
    (hlower : ∀ b, 0 < lower b)
    (hlowerLe : ∀ item, lower (positiveBin item) ≤ positiveArgument item)
    (hleUpper : ∀ item, positiveArgument item ≤ upper (positiveBin item))
    (hlowerLtUpper : ∀ b, lower b < upper b)
    (hnegativeWeight : ∀ item, 0 ≤ negativeWeight item)
    (hnegativeArgument : ∀ item, 0 < negativeArgument item)
    (hcenter : ∀ b, 0 < center b)
    (hlogTwoLowerPos : 0 < logTwoLower) (hlogTwoLower : logTwoLower ≤ Real.log 2)
    (hlogTwoUpper : Real.log 2 ≤ logTwoUpper) :
    chordTangentRationalValue constant positiveBin positiveWeight positiveArgument lower upper
        negativeBin negativeWeight negativeArgument center logTwoLower logTwoUpper ≤
      exactValue constant positiveWeight positiveArgument negativeWeight negativeArgument := by
  have hcompressed := chordTangentValue_le_exactValue constant positiveBin positiveWeight
    positiveArgument lower upper negativeBin negativeWeight negativeArgument center
    hpositiveWeight hlower hlowerLe hleUpper hlowerLtUpper hnegativeWeight hnegativeArgument
    hcenter
  have hresidual :
      inverseLogTwoFloor (tangentResidual negativeBin negativeWeight negativeArgument center)
          logTwoLower logTwoUpper ≤
        tangentResidual negativeBin negativeWeight negativeArgument center / Real.log 2 :=
    inverseLogTwoFloor_le hlogTwoLowerPos hlogTwoLower hlogTwoUpper
  unfold chordTangentRationalValue
  unfold chordTangentValue at hcompressed
  linarith

/-! ## The certificate interface

A generated certificate exhibits a rational `witness`, and a semantic theorem places the exact
log-linear form below the quantity the paper is really talking about.  The lemma below is the only
thing a client needs from this file: it composes the two with the compression inequality, so that
the compression itself never appears in the client's trust boundary.
-/

/-- **Certificate consumption form.**  A witness at most the compressed value of a chord/tangent
compression is at most any semantic quantity that dominates the exact value of the form. -/
theorem le_of_chordTangentCompression
    [Fintype Item] [Fintype ItemNeg] [Fintype Bin] [Fintype BinNeg]
    [DecidableEq Bin] [DecidableEq BinNeg]
    {witness semantic : ℝ}
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
    (hwitness : witness ≤
      chordTangentValue constant positiveBin positiveWeight positiveArgument lower upper
        negativeBin negativeWeight negativeArgument center)
    (hsemantic :
      exactValue constant positiveWeight positiveArgument negativeWeight negativeArgument ≤
        semantic) :
    witness ≤ semantic :=
  hwitness.trans
    ((chordTangentValue_le_exactValue constant positiveBin positiveWeight positiveArgument
      lower upper negativeBin negativeWeight negativeArgument center hpositiveWeight hlower
      hlowerLe hleUpper hlowerLtUpper hnegativeWeight hnegativeArgument hcenter).trans hsemantic)

end

end MatrixMultiplication.LogLinearCompression
