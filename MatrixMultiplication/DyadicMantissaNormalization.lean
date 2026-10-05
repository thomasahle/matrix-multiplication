/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicChordTangentCompression

/-!
# Odd-mantissa normalization of a signed log-linear form

`DyadicChordTangentCompression.lean` proves that the certificate exporter's chord/tangent
compression is a lower bound for the exact form.  What it does *not* yet describe is the exporter's
**last** step, `normalize_power_of_two_factors`
(`better_bound/export_simplified_exponent_scalar.py`): every surviving logarithm argument — a bin
endpoint or a bin centre — is a dyadic integer `2 ^ k · m` with `m` odd, and the exporter uses
`log₂ (2 ^ k · m) = k + log₂ m` to move `k · coefficient` into the constant and to pool the
remaining coefficients by the odd mantissa `m`.  That is what collapses tens of thousands of
distinct arguments onto the few dozen odd mantissas a generated data module actually stores.

The step is an *exact identity*, so it costs no slack; this module proves it, at an arbitrary
factorization and an arbitrary pooling.  Composed with the compression inequality it turns the
emitter's assertion "the committed arrays reproduce the chord expansion" into a finite
**rational** identity between coefficient arrays, with no logarithm and no re-indexing left in it.

## Contents

* `sum_fiberSum_mul` — the reindexing lemma behind every pooling step: a bin-indexed sum of fiber
  weights against a bin-indexed value equals the item-indexed sum against the value at the item's
  bin.
* `valuationShift` — the constant contributed by the powers of two, `Σᵢ wᵢ · kᵢ`.
* `sum_weighted_logTwo_eq_valuationShift_add_fiberSum` — normalization and pooling of one
  nonnegatively indexed family.
* `exactValue_eq_normalized` — the signed form: the exact value of a log-linear form equals the
  exact value of its odd-mantissa normalization, whose constant is shifted by the two valuation
  sums and whose coefficients are the mantissa fiber sums.
* `chordTangentCore_eq_exactValue` — the compressed core is itself a signed log-linear form, on
  the disjoint union of the two chord endpoint families.
* `chordTangentValue_eq_normalized` — the two previous theorems composed: the compressed value is
  the exact value of an odd-mantissa form plus the single residual multiple of `1 / log 2`.  This
  is the shape a generated certificate module commits.

## Position in the library

Paper layer (`MatrixMultiplication/`), directly above `DyadicChordTangentCompression.lean`.  No
declaration mentions a tensor, an exponent or a certificate: the factorization
`argument = 2 ^ valuation · mantissaValue` is a hypothesis, discharged by `decide` on the emitted
arrays in a generated client.
-/

open scoped BigOperators

namespace MatrixMultiplication.LogLinearCompression

universe u₁ v₁ v₂

noncomputable section

/-! ## The reindexing lemma -/

/-- **Pooling is reindexing.**  Summing fiber weights against a value attached to each bin is the
same as summing every item's weight against the value at that item's bin.

Both `binned_weighted_logTwo_chord_lower` and `neg_binned_weighted_logTwo_tangent_lower` perform
this step inline; naming it once makes every later normalization a rewrite. -/
theorem sum_fiberSum_mul {Item : Type u₁} {Bin : Type v₁}
    [Fintype Item] [Fintype Bin] [DecidableEq Bin]
    (bin : Item → Bin) (weight : Item → ℝ) (value : Bin → ℝ) :
    (∑ b : Bin, fiberSum bin weight b * value b) =
      ∑ item, weight item * value (bin item) := by
  classical
  calc (∑ b : Bin, fiberSum bin weight b * value b)
      = ∑ b : Bin, ∑ item : {item : Item // bin item = b}, weight item.1 * value b := by
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        unfold fiberSum
        rw [Finset.sum_mul]
    _ = ∑ b : Bin, ∑ item : {item : Item // bin item = b},
          weight item.1 * value (bin item.1) := by
        refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun item _ ↦ ?_
        rw [item.property]
    _ = ∑ item, weight item * value (bin item) :=
        Fintype.sum_fiberwise bin fun item ↦ weight item * value (bin item)

/-! ## Normalization of one family -/

/-- Constant contributed by moving each argument's power of two out of its logarithm. -/
def valuationShift {Item : Type u₁} [Fintype Item]
    (weight : Item → ℝ) (valuation : Item → ℕ) : ℝ :=
  ∑ item, weight item * (valuation item : ℝ)

/-- **Normalization and pooling of a weighted base-two logarithm sum.**  If every argument
factors as `2 ^ valuation · mantissaValue mantissa` with a positive mantissa value, the weighted
sum splits into an exact rational shift and a sum over mantissas only.

Neither positivity nor rationality of the weights is used, and the mantissa map may be arbitrary:
this is the exporter's `normalize_power_of_two_factors` regrouping, and it is an equality. -/
theorem sum_weighted_logTwo_eq_valuationShift_add_fiberSum
    {Item : Type u₁} {Mantissa : Type v₁}
    [Fintype Item] [Fintype Mantissa] [DecidableEq Mantissa]
    (weight argument : Item → ℝ)
    (valuation : Item → ℕ) (mantissa : Item → Mantissa) (mantissaValue : Mantissa → ℝ)
    (hmantissaValue : ∀ m, 0 < mantissaValue m)
    (hfactor : ∀ item,
      argument item = (2 : ℝ) ^ valuation item * mantissaValue (mantissa item)) :
    (∑ item, weight item * (Real.log (argument item) / Real.log 2)) =
      valuationShift weight valuation +
        ∑ m : Mantissa,
          fiberSum mantissa weight m * (Real.log (mantissaValue m) / Real.log 2) := by
  have hterm : ∀ item,
      Real.log (argument item) / Real.log 2 =
        (valuation item : ℝ) + Real.log (mantissaValue (mantissa item)) / Real.log 2 := by
    intro item
    rw [hfactor item]
    exact logTwo_two_pow_mul (valuation item) (hmantissaValue (mantissa item))
  rw [sum_fiberSum_mul mantissa weight fun m ↦ Real.log (mantissaValue m) / Real.log 2,
    valuationShift, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun item _ ↦ ?_
  rw [hterm item]
  ring

/-! ## Normalization of the signed form -/

/-- **The exporter's normalization, as an identity on signed log-linear forms.**  The exact value
of a form is the exact value of its odd-mantissa normalization: the constant absorbs the two
valuation shifts, and each mantissa carries the fiber sum of the coefficients pooled onto it.

Because the identity is exact, the emitter assertion it discharges — "the committed coefficient
arrays reproduce the regrouping" — is a finite *rational* statement with no logarithm in it. -/
theorem exactValue_eq_normalized
    {Item ItemNeg : Type u₁} {PosMantissa NegMantissa : Type v₁}
    [Fintype Item] [Fintype ItemNeg] [Fintype PosMantissa] [Fintype NegMantissa]
    [DecidableEq PosMantissa] [DecidableEq NegMantissa]
    (constant : ℝ)
    (positiveWeight positiveArgument : Item → ℝ)
    (negativeWeight negativeArgument : ItemNeg → ℝ)
    (positiveValuation : Item → ℕ) (positiveMantissa : Item → PosMantissa)
    (positiveMantissaValue : PosMantissa → ℝ)
    (negativeValuation : ItemNeg → ℕ) (negativeMantissa : ItemNeg → NegMantissa)
    (negativeMantissaValue : NegMantissa → ℝ)
    (hpositiveMantissaValue : ∀ m, 0 < positiveMantissaValue m)
    (hnegativeMantissaValue : ∀ m, 0 < negativeMantissaValue m)
    (hpositiveFactor : ∀ item, positiveArgument item =
      (2 : ℝ) ^ positiveValuation item * positiveMantissaValue (positiveMantissa item))
    (hnegativeFactor : ∀ item, negativeArgument item =
      (2 : ℝ) ^ negativeValuation item * negativeMantissaValue (negativeMantissa item)) :
    exactValue constant positiveWeight positiveArgument negativeWeight negativeArgument =
      exactValue
        (constant + valuationShift positiveWeight positiveValuation -
          valuationShift negativeWeight negativeValuation)
        (fiberSum positiveMantissa positiveWeight) positiveMantissaValue
        (fiberSum negativeMantissa negativeWeight) negativeMantissaValue := by
  have hpositive := sum_weighted_logTwo_eq_valuationShift_add_fiberSum
    positiveWeight positiveArgument positiveValuation positiveMantissa positiveMantissaValue
    hpositiveMantissaValue hpositiveFactor
  have hnegative := sum_weighted_logTwo_eq_valuationShift_add_fiberSum
    negativeWeight negativeArgument negativeValuation negativeMantissa negativeMantissaValue
    hnegativeMantissaValue hnegativeFactor
  unfold exactValue
  rw [hpositive, hnegative]
  ring

/-! ## The compressed core is a signed log-linear form -/

/-- **The compressed core, re-read as a form.**  Everything in the compression except the residual
is itself the exact value of a signed log-linear form: its positive family is the disjoint union
of the two chord endpoint families, its negative family is the pooled bin weights, and its
arguments are the endpoints and centres. -/
theorem chordTangentCore_eq_exactValue
    {Item ItemNeg : Type u₁} {Bin BinNeg : Type v₁}
    [Fintype Item] [Fintype ItemNeg] [Fintype Bin] [Fintype BinNeg]
    [DecidableEq Bin] [DecidableEq BinNeg]
    (constant : ℝ)
    (positiveBin : Item → Bin) (positiveWeight positiveArgument : Item → ℝ)
    (lower upper : Bin → ℝ)
    (negativeBin : ItemNeg → BinNeg) (negativeWeight : ItemNeg → ℝ)
    (center : BinNeg → ℝ) :
    chordTangentCore constant positiveBin positiveWeight positiveArgument lower upper
        negativeBin negativeWeight center =
      exactValue constant
        (Sum.elim (chordLowerCoefficient positiveBin positiveWeight positiveArgument lower upper)
          (chordUpperCoefficient positiveBin positiveWeight positiveArgument lower upper))
        (Sum.elim lower upper)
        (fiberSum negativeBin negativeWeight) center := by
  have hsum :
      (∑ x : Bin ⊕ Bin,
        Sum.elim (chordLowerCoefficient positiveBin positiveWeight positiveArgument lower upper)
            (chordUpperCoefficient positiveBin positiveWeight positiveArgument lower upper) x *
          (Real.log (Sum.elim lower upper x) / Real.log 2)) =
        ∑ b : Bin,
          (chordLowerCoefficient positiveBin positiveWeight positiveArgument lower upper b *
              (Real.log (lower b) / Real.log 2) +
            chordUpperCoefficient positiveBin positiveWeight positiveArgument lower upper b *
              (Real.log (upper b) / Real.log 2)) := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact Finset.sum_add_distrib.symm
  unfold chordTangentCore exactValue
  rw [hsum]

/-- **The committed shape.**  The chord/tangent compressed value is the exact value of an
odd-mantissa signed log-linear form plus the single residual multiple of `1 / log 2` — exactly the
constant, two coefficient arrays and one residual coefficient that a generated certificate module
stores.

The two factorization hypotheses are `decide`-level checks on the emitted endpoint and centre
arrays; nothing else about the concrete data is used. -/
theorem chordTangentValue_eq_normalized
    {Item ItemNeg : Type u₁} {Bin BinNeg : Type v₁} {PosMantissa NegMantissa : Type v₂}
    [Fintype Item] [Fintype ItemNeg] [Fintype Bin] [Fintype BinNeg]
    [DecidableEq Bin] [DecidableEq BinNeg]
    [Fintype PosMantissa] [Fintype NegMantissa]
    [DecidableEq PosMantissa] [DecidableEq NegMantissa]
    (constant : ℝ)
    (positiveBin : Item → Bin) (positiveWeight positiveArgument : Item → ℝ)
    (lower upper : Bin → ℝ)
    (negativeBin : ItemNeg → BinNeg) (negativeWeight negativeArgument : ItemNeg → ℝ)
    (center : BinNeg → ℝ)
    (endpointValuation : Bin ⊕ Bin → ℕ) (endpointMantissa : Bin ⊕ Bin → PosMantissa)
    (endpointMantissaValue : PosMantissa → ℝ)
    (centerValuation : BinNeg → ℕ) (centerMantissa : BinNeg → NegMantissa)
    (centerMantissaValue : NegMantissa → ℝ)
    (hendpointMantissaValue : ∀ m, 0 < endpointMantissaValue m)
    (hcenterMantissaValue : ∀ m, 0 < centerMantissaValue m)
    (hendpointFactor : ∀ x, Sum.elim lower upper x =
      (2 : ℝ) ^ endpointValuation x * endpointMantissaValue (endpointMantissa x))
    (hcenterFactor : ∀ b, center b =
      (2 : ℝ) ^ centerValuation b * centerMantissaValue (centerMantissa b)) :
    chordTangentValue constant positiveBin positiveWeight positiveArgument lower upper
        negativeBin negativeWeight negativeArgument center =
      exactValue
        (constant +
            valuationShift
              (Sum.elim
                (chordLowerCoefficient positiveBin positiveWeight positiveArgument lower upper)
                (chordUpperCoefficient positiveBin positiveWeight positiveArgument lower upper))
              endpointValuation -
            valuationShift (fiberSum negativeBin negativeWeight) centerValuation)
          (fiberSum endpointMantissa
            (Sum.elim
              (chordLowerCoefficient positiveBin positiveWeight positiveArgument lower upper)
              (chordUpperCoefficient positiveBin positiveWeight positiveArgument lower upper)))
          endpointMantissaValue
          (fiberSum centerMantissa (fiberSum negativeBin negativeWeight)) centerMantissaValue +
        tangentResidual negativeBin negativeWeight negativeArgument center / Real.log 2 := by
  unfold chordTangentValue
  rw [chordTangentCore_eq_exactValue constant positiveBin positiveWeight positiveArgument
    lower upper negativeBin negativeWeight center,
    exactValue_eq_normalized constant
      (Sum.elim
        (chordLowerCoefficient positiveBin positiveWeight positiveArgument lower upper)
        (chordUpperCoefficient positiveBin positiveWeight positiveArgument lower upper))
      (Sum.elim lower upper) (fiberSum negativeBin negativeWeight) center
      endpointValuation endpointMantissa endpointMantissaValue
      centerValuation centerMantissa centerMantissaValue
      hendpointMantissaValue hcenterMantissaValue hendpointFactor hcenterFactor]

end

end MatrixMultiplication.LogLinearCompression
