/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicMantissaNormalization

/-!
# Rational and integral accumulation of the compression bookkeeping

`DyadicChordTangentCompression.lean` and `DyadicMantissaNormalization.lean` reduce a compressed
certificate witness to four finite statements about the emitted arrays: one constant identity, two
coefficient-family identities and one residual identity.  All four are stated in `ℝ`, because that
is where the logarithms live — but *none of them contains a logarithm*.  They are sums, products
and quotients of rationals, and `norm_num` cannot evaluate a `ℝ`-valued fibre sum over thousands
of items while `decide` does not apply to `ℝ` at all.

This module is the data-independent half of the fix: every ingredient of the bookkeeping —
the fibre sum, the valuation shift, the two chord coefficients and the tangent residual — is
defined here over an arbitrary carrier, and the `ℝ`-valued definition of the generic API is
proved to be the *cast* of the `ℚ`-valued one.  A future chunked accumulation may therefore
discharge the four hypotheses in `ℚ`, or — after `fiberSumIn_div` pulls out the common
denominator `2 ^ (bits + maxShift)` — in `ℤ`, where a kernel `decide` is available and where no
`gcd` normalisation is performed.

Nothing here mentions a certificate, a tensor or an exponent, and no declaration needs the
concrete arrays: the statements are about the generic compression vocabulary only.

## Contents

* `fiberSumIn`, `valuationShiftIn`, `chordLowerCoefficientIn`, `chordUpperCoefficientIn`,
  `tangentResidualIn` — the five bookkeeping operations at an arbitrary carrier, agreeing with
  the `ℝ`-valued definitions of `LogLinearCompressionFamily` / `DyadicChordTangentCompression`
  by `rfl` (`fiberSum_eq_fiberSumIn`, `valuationShift_eq_valuationShiftIn`, …).
* `fiberSumIn_map` — pooling commutes with any additive map; every cast bridge below is an
  instance of it.
* `fiberSum_ratCast`, `valuationShift_ratCast`, `chordLowerCoefficient_ratCast`,
  `chordUpperCoefficient_ratCast`, `tangentResidual_ratCast` — the `ℝ`-valued bookkeeping of a
  cast-`ℚ` family is the cast of the `ℚ`-valued bookkeeping.
* `fiberSumIn_div`, `fiberSumIn_intCast`, `fiberSum_intCast_div` — the integral accumulator: a
  fibre sum of integers over a fixed common denominator is the cast of one integer sum divided by
  that denominator.

## Position in the library

Paper layer (`MatrixMultiplication/`), directly above `DyadicMantissaNormalization.lean`, whose
`valuationShift` it also lifts.  It is certificate-independent and reusable by every compression
seam.
-/

open scoped BigOperators

set_option autoImplicit false

namespace MatrixMultiplication.LogLinearCompression

universe u v w

/-! ## The bookkeeping at an arbitrary carrier

The five definitions below are the `ℝ`-valued ones of the generic compression API with the
carrier made a parameter.  Each agrees with the original by `rfl`, so a rewrite in either
direction is free.
-/

/-- **Pooling at an arbitrary carrier.**  `fiberSum` restricted to `ℝ`; the accumulator that a
chunked kernel computation wants is `ℚ` or `ℤ`. -/
def fiberSumIn {M : Type w} [AddCommMonoid M] {Item : Type u} {Bin : Type v}
    [Fintype Item] [DecidableEq Bin] (bin : Item → Bin) (term : Item → M) (b : Bin) : M :=
  ∑ item : {item : Item // bin item = b}, term item.1

theorem fiberSum_eq_fiberSumIn {Item : Type u} {Bin : Type v}
    [Fintype Item] [DecidableEq Bin] (bin : Item → Bin) (term : Item → ℝ) (b : Bin) :
    fiberSum bin term b = fiberSumIn bin term b := rfl

/-- The valuation shift at an arbitrary carrier. -/
def valuationShiftIn {R : Type w} [Semiring R] {Item : Type u} [Fintype Item]
    (weight : Item → R) (valuation : Item → ℕ) : R :=
  ∑ item, weight item * (valuation item : R)

theorem valuationShift_eq_valuationShiftIn {Item : Type u} [Fintype Item]
    (weight : Item → ℝ) (valuation : Item → ℕ) :
    valuationShift weight valuation = valuationShiftIn weight valuation := rfl

/-- The lower chord coefficient of one bin at an arbitrary carrier. -/
def chordLowerCoefficientIn {K : Type w} [DivisionRing K] {Item : Type u} {Bin : Type v}
    [Fintype Item] [DecidableEq Bin]
    (bin : Item → Bin) (weight argument : Item → K) (lower upper : Bin → K) (b : Bin) : K :=
  fiberSumIn bin (fun item ↦ weight item * ((upper b - argument item) / (upper b - lower b))) b

theorem chordLowerCoefficient_eq_chordLowerCoefficientIn {Item : Type u} {Bin : Type v}
    [Fintype Item] [DecidableEq Bin]
    (bin : Item → Bin) (weight argument : Item → ℝ) (lower upper : Bin → ℝ) (b : Bin) :
    chordLowerCoefficient bin weight argument lower upper b =
      chordLowerCoefficientIn bin weight argument lower upper b := rfl

/-- The upper chord coefficient of one bin at an arbitrary carrier. -/
def chordUpperCoefficientIn {K : Type w} [DivisionRing K] {Item : Type u} {Bin : Type v}
    [Fintype Item] [DecidableEq Bin]
    (bin : Item → Bin) (weight argument : Item → K) (lower upper : Bin → K) (b : Bin) : K :=
  fiberSumIn bin (fun item ↦ weight item * ((argument item - lower b) / (upper b - lower b))) b

theorem chordUpperCoefficient_eq_chordUpperCoefficientIn {Item : Type u} {Bin : Type v}
    [Fintype Item] [DecidableEq Bin]
    (bin : Item → Bin) (weight argument : Item → ℝ) (lower upper : Bin → ℝ) (b : Bin) :
    chordUpperCoefficient bin weight argument lower upper b =
      chordUpperCoefficientIn bin weight argument lower upper b := rfl

/-- The pooled first-order tangent remainder at an arbitrary carrier. -/
def tangentResidualIn {K : Type w} [DivisionRing K] {ItemNeg : Type u} {BinNeg : Type v}
    [Fintype ItemNeg] (negativeBin : ItemNeg → BinNeg)
    (negativeWeight negativeArgument : ItemNeg → K) (center : BinNeg → K) : K :=
  -∑ item, negativeWeight item * (negativeArgument item / center (negativeBin item) - 1)

theorem tangentResidual_eq_tangentResidualIn {ItemNeg : Type u} {BinNeg : Type v}
    [Fintype ItemNeg] (negativeBin : ItemNeg → BinNeg)
    (negativeWeight negativeArgument : ItemNeg → ℝ) (center : BinNeg → ℝ) :
    tangentResidual negativeBin negativeWeight negativeArgument center =
      tangentResidualIn negativeBin negativeWeight negativeArgument center := rfl

/-! ## Pooling commutes with an additive map -/

/-- **The one lemma behind every cast bridge.**  A fibre sum is a finite sum, so any additive map
passes through it.  Instantiating at `Rat.castHom ℝ` moves the pooling from `ℝ` into `ℚ`; at
`Int.castRingHom ℚ` it moves from `ℚ` into `ℤ`. -/
theorem fiberSumIn_map {M : Type w} {N : Type w} [AddCommMonoid M] [AddCommMonoid N]
    {Item : Type u} {Bin : Type v} [Fintype Item] [DecidableEq Bin]
    (f : M →+ N) (bin : Item → Bin) (term : Item → M) (b : Bin) :
    f (fiberSumIn bin term b) = fiberSumIn bin (fun item ↦ f (term item)) b :=
  map_sum f _ _

/-! ## The `ℚ`-cast bridges

Each statement says: the `ℝ`-valued bookkeeping of a family that is *itself* a cast of rational
data equals the cast of the `ℚ`-valued bookkeeping of that data.  So the four hypotheses of a
`…_of_normalizedChordTangentCompression` theorem may be discharged entirely inside `ℚ`.
-/

/-- **The fibre-sum cast bridge.**  Pooling a cast-`ℚ` family in `ℝ` is the cast of pooling it in
`ℚ`. -/
theorem fiberSum_ratCast {Item : Type u} {Bin : Type v} [Fintype Item] [DecidableEq Bin]
    (bin : Item → Bin) (weight : Item → ℚ) (b : Bin) :
    fiberSum bin (fun item ↦ ((weight item : ℚ) : ℝ)) b =
      ((fiberSumIn bin weight b : ℚ) : ℝ) := by
  simp only [fiberSum, fiberSumIn, Rat.cast_sum]

/-- The valuation-shift cast bridge. -/
theorem valuationShift_ratCast {Item : Type u} [Fintype Item]
    (weight : Item → ℚ) (valuation : Item → ℕ) :
    valuationShift (fun item ↦ ((weight item : ℚ) : ℝ)) valuation =
      ((valuationShiftIn weight valuation : ℚ) : ℝ) := by
  simp only [valuationShift, valuationShiftIn, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast]

/-- The lower-chord-coefficient cast bridge. -/
theorem chordLowerCoefficient_ratCast {Item : Type u} {Bin : Type v}
    [Fintype Item] [DecidableEq Bin]
    (bin : Item → Bin) (weight argument : Item → ℚ) (lower upper : Bin → ℚ) (b : Bin) :
    chordLowerCoefficient bin (fun item ↦ ((weight item : ℚ) : ℝ))
        (fun item ↦ ((argument item : ℚ) : ℝ)) (fun b ↦ ((lower b : ℚ) : ℝ))
        (fun b ↦ ((upper b : ℚ) : ℝ)) b =
      ((chordLowerCoefficientIn bin weight argument lower upper b : ℚ) : ℝ) := by
  simp only [chordLowerCoefficient, chordLowerCoefficientIn, fiberSum, fiberSumIn,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_sub]

/-- The upper-chord-coefficient cast bridge. -/
theorem chordUpperCoefficient_ratCast {Item : Type u} {Bin : Type v}
    [Fintype Item] [DecidableEq Bin]
    (bin : Item → Bin) (weight argument : Item → ℚ) (lower upper : Bin → ℚ) (b : Bin) :
    chordUpperCoefficient bin (fun item ↦ ((weight item : ℚ) : ℝ))
        (fun item ↦ ((argument item : ℚ) : ℝ)) (fun b ↦ ((lower b : ℚ) : ℝ))
        (fun b ↦ ((upper b : ℚ) : ℝ)) b =
      ((chordUpperCoefficientIn bin weight argument lower upper b : ℚ) : ℝ) := by
  simp only [chordUpperCoefficient, chordUpperCoefficientIn, fiberSum, fiberSumIn,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_sub]

/-- The residual cast bridge: the emitted `1 / log 2` coefficient is a rational computation. -/
theorem tangentResidual_ratCast {ItemNeg : Type u} {BinNeg : Type v} [Fintype ItemNeg]
    (negativeBin : ItemNeg → BinNeg) (negativeWeight negativeArgument : ItemNeg → ℚ)
    (center : BinNeg → ℚ) :
    tangentResidual negativeBin (fun item ↦ ((negativeWeight item : ℚ) : ℝ))
        (fun item ↦ ((negativeArgument item : ℚ) : ℝ)) (fun b ↦ ((center b : ℚ) : ℝ)) =
      ((tangentResidualIn negativeBin negativeWeight negativeArgument center : ℚ) : ℝ) := by
  simp only [tangentResidual, tangentResidualIn, Rat.cast_neg, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_div, Rat.cast_sub, Rat.cast_one]

/-! ## The integral accumulator

A chunked kernel computation must not accumulate in `ℚ`: every partial sum would be `gcd`-
normalised.  The emitted data has a fixed common denominator — `2 ^ (bits + maxShift)` for the
scalar payloads — so the accumulation is a sum of *integers* divided once at the end.
-/

/-- A common denominator factors out of a fibre sum. -/
theorem fiberSumIn_div {K : Type w} [DivisionRing K] {Item : Type u} {Bin : Type v}
    [Fintype Item] [DecidableEq Bin]
    (bin : Item → Bin) (term : Item → K) (denominator : K) (b : Bin) :
    fiberSumIn bin (fun item ↦ term item / denominator) b =
      fiberSumIn bin term b / denominator :=
  (Finset.sum_div _ _ _).symm

/-- Pooling a cast-`ℤ` family in `ℝ` is the cast of pooling it in `ℤ`. -/
theorem fiberSumIn_intCast {Item : Type u} {Bin : Type v} [Fintype Item] [DecidableEq Bin]
    (bin : Item → Bin) (numerator : Item → ℤ) (b : Bin) :
    fiberSumIn bin (fun item ↦ ((numerator item : ℤ) : ℝ)) b =
      ((fiberSumIn bin numerator b : ℤ) : ℝ) := by
  simp only [fiberSumIn, Int.cast_sum]

/-- **The shape a chunked accumulation produces.**  With the emitted numerators integral over one
fixed denominator, the `ℝ`-valued fibre sum of the family is the cast of a single integer sum,
divided once.  Everything left to check is then an identity between integers, in reach of the
kernel. -/
theorem fiberSum_intCast_div {Item : Type u} {Bin : Type v} [Fintype Item] [DecidableEq Bin]
    (bin : Item → Bin) (numerator : Item → ℤ) (denominator : ℝ) (b : Bin) :
    fiberSum bin (fun item ↦ ((numerator item : ℤ) : ℝ) / denominator) b =
      ((fiberSumIn bin numerator b : ℤ) : ℝ) / denominator := by
  rw [fiberSum_eq_fiberSumIn, fiberSumIn_div bin (fun item ↦ ((numerator item : ℤ) : ℝ))
    denominator b, fiberSumIn_intCast]

end MatrixMultiplication.LogLinearCompression
