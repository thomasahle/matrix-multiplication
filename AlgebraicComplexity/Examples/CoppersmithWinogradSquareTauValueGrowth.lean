/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.NormalizedPower
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareOuterGrowth
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareTauValueAssembly
import AlgebraicComplexity.MatrixMultiplication.CyclicValueNormalization

/-!
# Stable lower terms for the CW-square `τ`-value assembly

This module is the numerical/asymptotic bridge between the exact finite outer assembly and any
cyclic inner degeneration certificate.  It deliberately knows nothing about how the inner
certificate was produced.  Its inputs are only:

* a lower bound `outerBase^k` on the number of outer survivors;
* a positive lower bound `innerTerm` on the normalized cyclic inner term; and
* the exact compatibility equation `inner.power = d*k`.

The output is a repetition-independent lower bound on the assembled plain `τ`-value certificate:

```text
(outerBase * ordinaryVolume^τ * innerTerm^(3*d))^(1 / outerStride).
```

Thus future clients may replace the inner zeroing/hash construction by any stronger restriction
or polynomial degeneration without changing the outer proof or its normalization.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u w

/-! ## Repetition-independent numerical term -/

/-- One-repetition side contributed by all ordinary CW-square constituent orbits. -/
def cwSquareOrdinaryDimensionBase (q b c : ℕ) : ℕ :=
  (2 * q) ^ (2 * b) * (q ^ 2 + 2) ^ c

/-- The finite ordinary side is the corresponding one-repetition side raised to `k`. -/
theorem cwSquareOrdinaryDimension_eq_base_pow (q b c k : ℕ) :
    cwSquareOrdinaryDimension q b c k =
      cwSquareOrdinaryDimensionBase q b c ^ k := by
  unfold cwSquareOrdinaryDimension cwSquareOrdinaryDimensionBase
  conv_rhs => rw [mul_pow, ← pow_mul, ← pow_mul]

/-- The one-repetition ordinary side is positive when `q` is positive. -/
theorem cwSquareOrdinaryDimensionBase_pos
    {q b c : ℕ} (hq : 0 < q) :
    0 < cwSquareOrdinaryDimensionBase q b c := by
  unfold cwSquareOrdinaryDimensionBase
  positivity

/-- Logarithm of the one-repetition ordinary cube volume, expanded into the two elementary CW
constituent dimensions. -/
theorem log_cwSquareOrdinaryVolume
    (q b c : ℕ) (hq : 0 < q) :
    Real.log
        ((cwSquareOrdinaryDimensionBase q b c *
          cwSquareOrdinaryDimensionBase q b c *
          cwSquareOrdinaryDimensionBase q b c : ℕ) : ℝ) =
      (6 * b : ℝ) * Real.log (2 * q : ℕ) +
        (3 * c : ℝ) * Real.log (q ^ 2 + 2 : ℕ) := by
  have htwoQ : (0 : ℝ) < (2 * q : ℕ) := by exact_mod_cast Nat.mul_pos (by norm_num) hq
  have hlarge : (0 : ℝ) < (q ^ 2 + 2 : ℕ) := by positivity
  unfold cwSquareOrdinaryDimensionBase
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring

/-- Repetition-independent lower term for a CW-square value assembly.

`outerBase` is the exponential base of the outer survivor count.  `innerTerm` is a lower bound on
the *normalized cyclic* value of the exceptional constituent, hence its unnormalized contribution
over `d*k` inner powers is `innerTerm^(3*d*k)`. -/
noncomputable def cwSquareTauValueLimitLowerTerm
    (outerBase innerTerm τ : ℝ) (q a b c d : ℕ) : ℝ :=
  (outerBase *
      ((((cwSquareOrdinaryDimensionBase q b c *
          cwSquareOrdinaryDimensionBase q b c *
          cwSquareOrdinaryDimensionBase q b c : ℕ) : ℝ) ^ τ) *
        innerTerm ^ (((3 * d : ℕ) : ℝ)))) ^
    (((cwSquareStride a b c d : ℕ) : ℝ)⁻¹)

/-- Finite `k`-repetition version of `cwSquareTauValueLimitLowerTerm`. -/
noncomputable def cwSquareTauValueFiniteLowerTerm
    (outerBase innerTerm τ : ℝ) (q a b c d k : ℕ) : ℝ :=
  ((outerBase ^ k) *
      ((((cwSquareOrdinaryDimension q b c k *
          cwSquareOrdinaryDimension q b c k *
          cwSquareOrdinaryDimension q b c k : ℕ) : ℝ) ^ τ) *
        innerTerm ^ (((3 * (d * k) : ℕ) : ℝ)))) ^
    (((cwSquareDepth a b c d k + 1 : ℕ) : ℝ)⁻¹)

/-- Proportional repetition disappears from the finite square lower term.

Proof sketch: the ordinary side is a `k`th power, the cyclic inner contribution is the `k`th
power of `innerTerm^(3*d)`, and the outer count contributes `outerBase^k`.  Hence the complete
quantity below the root is a `k`th power.  The exact depth identity changes the root exponent to
`1/(stride*k)`, and `normalizedRepeatedPower_eq` cancels `k`. -/
theorem cwSquareTauValueFiniteLowerTerm_eq_limit
    (outerBase innerTerm τ : ℝ) (q a b c d k : ℕ)
    (houter : 0 < outerBase) (hinner : 0 < innerTerm)
    (hq : 0 < q) (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k) :
    cwSquareTauValueFiniteLowerTerm outerBase innerTerm τ q a b c d k =
      cwSquareTauValueLimitLowerTerm outerBase innerTerm τ q a b c d := by
  let D := cwSquareOrdinaryDimensionBase q b c
  let volume : ℕ := D * D * D
  let stableBase : ℝ :=
    outerBase * (((volume : ℕ) : ℝ) ^ τ * innerTerm ^ (((3 * d : ℕ) : ℝ)))
  have hD : 0 < D := cwSquareOrdinaryDimensionBase_pos hq
  have hvolumeNat : 0 < volume := Nat.mul_pos (Nat.mul_pos hD hD) hD
  have hvolume : (0 : ℝ) < (volume : ℕ) := by exact_mod_cast hvolumeNat
  have hstable : 0 < stableBase := by
    unfold stableBase
    exact mul_pos houter
      (mul_pos (Real.rpow_pos_of_pos hvolume τ)
        (Real.rpow_pos_of_pos hinner _))
  have hordinary :
      (((cwSquareOrdinaryDimension q b c k *
          cwSquareOrdinaryDimension q b c k *
          cwSquareOrdinaryDimension q b c k : ℕ) : ℝ) ^ τ) =
        ((((volume : ℕ) : ℝ) ^ τ) ^ k) := by
    rw [cwSquareOrdinaryDimension_eq_base_pow]
    have hnat : D ^ k * D ^ k * D ^ k = volume ^ k := by
      simp only [volume, mul_pow]
    change ((((D ^ k * D ^ k * D ^ k : ℕ) : ℝ) ^ τ)) = _
    rw [hnat, Nat.cast_pow]
    exact (Real.rpow_pow_comm (Nat.cast_nonneg volume) τ k).symm
  have hinnerPower :
      innerTerm ^ (((3 * (d * k) : ℕ) : ℝ)) =
        (innerTerm ^ (((3 * d : ℕ) : ℝ))) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hinner.le]
    congr 1
    push_cast
    ring
  unfold cwSquareTauValueFiniteLowerTerm cwSquareTauValueLimitLowerTerm
  rw [cwSquareDepth_add_one hstride hk, hordinary, hinnerPower]
  change ((outerBase ^ k) *
      ((((volume : ℕ) : ℝ) ^ τ) ^ k *
        (innerTerm ^ (((3 * d : ℕ) : ℝ))) ^ k)) ^
      ((((cwSquareStride a b c d * k : ℕ) : ℝ))⁻¹) =
    stableBase ^ (((cwSquareStride a b c d : ℕ) : ℝ)⁻¹)
  rw [← mul_pow, ← mul_pow]
  exact normalizedRepeatedPower_eq stableBase (cwSquareStride a b c d) k
    hstable hstride hk

/-- Logarithmic sufficient condition for a strict stable square-value inequality.

For positive inputs, the nested real-power comparison

```text
budget < (outerBase * ordinaryVolume^τ * innerTerm^(3*d))^(1/stride)
```

is implied by the linear logarithmic inequality displayed in the hypothesis.  This is the
preferred interface for exact-rational numerical clients, which can bound each logarithm in the
direction needed without evaluating any real power.

Proof sketch: expand the logarithm of the positive stable term, divide the hypothesis by the
positive stride, and use strict monotonicity of `exp`. -/
theorem lt_cwSquareTauValueLimitLowerTerm_of_log_lt
    (budget outerBase innerTerm τ : ℝ) (q a b c d : ℕ)
    (hbudget : 0 < budget) (houter : 0 < outerBase) (hinner : 0 < innerTerm)
    (hq : 0 < q) (hstride : 0 < cwSquareStride a b c d)
    (hlog : ((cwSquareStride a b c d : ℕ) : ℝ) * Real.log budget <
      Real.log outerBase +
        τ * Real.log
          ((cwSquareOrdinaryDimensionBase q b c *
            cwSquareOrdinaryDimensionBase q b c *
            cwSquareOrdinaryDimensionBase q b c : ℕ) : ℝ) +
        ((3 * d : ℕ) : ℝ) * Real.log innerTerm) :
    budget < cwSquareTauValueLimitLowerTerm outerBase innerTerm τ q a b c d := by
  let volume : ℕ :=
    cwSquareOrdinaryDimensionBase q b c *
      cwSquareOrdinaryDimensionBase q b c *
      cwSquareOrdinaryDimensionBase q b c
  have hD : 0 < cwSquareOrdinaryDimensionBase q b c :=
    cwSquareOrdinaryDimensionBase_pos hq
  have hvolumeNat : 0 < volume := Nat.mul_pos (Nat.mul_pos hD hD) hD
  have hvolume : (0 : ℝ) < (volume : ℕ) := by exact_mod_cast hvolumeNat
  let base : ℝ := outerBase * (((volume : ℕ) : ℝ) ^ τ *
    innerTerm ^ (((3 * d : ℕ) : ℝ)))
  have hbase : 0 < base := by
    unfold base
    exact mul_pos houter
      (mul_pos (Real.rpow_pos_of_pos hvolume τ)
        (Real.rpow_pos_of_pos hinner _))
  have hterm : 0 < cwSquareTauValueLimitLowerTerm
      outerBase innerTerm τ q a b c d := by
    unfold cwSquareTauValueLimitLowerTerm
    exact Real.rpow_pos_of_pos hbase _
  have hlogTerm :
      Real.log (cwSquareTauValueLimitLowerTerm
        outerBase innerTerm τ q a b c d) =
        (((cwSquareStride a b c d : ℕ) : ℝ)⁻¹) *
          (Real.log outerBase + τ * Real.log (volume : ℝ) +
            ((3 * d : ℕ) : ℝ) * Real.log innerTerm) := by
    unfold cwSquareTauValueLimitLowerTerm
    rw [Real.log_rpow hbase]
    unfold base
    rw [Real.log_mul houter.ne' (mul_pos
      (Real.rpow_pos_of_pos hvolume τ)
      (Real.rpow_pos_of_pos hinner _)).ne',
      Real.log_mul (Real.rpow_pos_of_pos hvolume τ).ne'
        (Real.rpow_pos_of_pos hinner _).ne',
      Real.log_rpow hvolume, Real.log_rpow hinner]
    ring
  have hstrideReal : (0 : ℝ) < cwSquareStride a b c d := by exact_mod_cast hstride
  have hlog' : Real.log budget <
      (((cwSquareStride a b c d : ℕ) : ℝ)⁻¹) *
        (Real.log outerBase + τ * Real.log (volume : ℝ) +
          ((3 * d : ℕ) : ℝ) * Real.log innerTerm) := by
    rw [inv_mul_eq_div, lt_div_iff₀ hstrideReal]
    simpa only [volume, mul_comm] using hlog
  calc
    budget = Real.exp (Real.log budget) := (Real.exp_log hbudget).symm
    _ < Real.exp (Real.log (cwSquareTauValueLimitLowerTerm
          outerBase innerTerm τ q a b c d)) := by
      exact Real.exp_lt_exp.mpr (by simpa only [hlogTerm] using hlog')
    _ = cwSquareTauValueLimitLowerTerm outerBase innerTerm τ q a b c d :=
      Real.exp_log hterm

/-! ## Comparison with an actual finite assembly -/

noncomputable section

variable (K : Type u) [CommRing K]

/-- A finite outer-count lower bound and a normalized inner-value lower bound give the matching
finite lower bound on the assembled square certificate.

This theorem is relation-neutral on the inner side: `inner` may be produced by any polynomial
degeneration.  No zeroing operation is mentioned in either the statement or proof.

Proof sketch: raise `innerTerm ≤ inner.term` to `3*inner.power` using the generic cyclic
normalization theorem, obtaining a bound on the unnormalized inner volume sum.  Multiply it by
the outer survivor and ordinary-volume bounds, then apply monotonicity of the final root. -/
theorem cwSquareTauValueFiniteLowerTerm_le_certificate
    {R : Type w} [Field R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (outerBase innerTerm τ : ℝ) (q a b c d k : ℕ)
    (houterBase : 0 ≤ outerBase) (hinnerTerm : 0 ≤ innerTerm)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hd : 0 < d) (hk : 0 < k)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1)))
    [Nonempty (CWSquareOuterSurvivor H a b c d k B seed)]
    (houterCopies : outerBase ^ k ≤
      (Fintype.card (CWSquareOuterSurvivor H a b c d k B seed) : ℝ))
    (inner : CyclicDegenerationCertificate K
      (cw112PartitionedTensor K q).realize τ)
    (hinnerPower : inner.power = d * k)
    (hinner : innerTerm ≤ inner.term) :
    cwSquareTauValueFiniteLowerTerm outerBase innerTerm τ q a b c d k ≤
      (cwSquareTauValueCertificateOfCyclicInner
        K H τ q a b c d k hq hordinary hd hk B hB seed inner hinnerPower).term τ := by
  rw [cwSquareTauValueCertificateOfCyclicInner_term]
  unfold cwSquareTauValueFiniteLowerTerm
  apply Real.rpow_le_rpow
  · exact mul_nonneg (pow_nonneg houterBase k)
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) τ)
        (Real.rpow_nonneg hinnerTerm _))
  · have hinnerSum :=
      inner.rpow_three_mul_power_le_volumePowerSum K hinnerTerm hinner
    rw [hinnerPower] at hinnerSum
    exact mul_le_mul houterCopies
      (mul_le_mul_of_nonneg_left hinnerSum
        (Real.rpow_nonneg (Nat.cast_nonneg _) τ))
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) τ)
        (Real.rpow_nonneg hinnerTerm _))
      (Nat.cast_nonneg _)
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Stable form of `cwSquareTauValueFiniteLowerTerm_le_certificate`: after exact proportional
normalization, the lower bound no longer depends on `k`. -/
theorem cwSquareTauValueLimitLowerTerm_le_certificate
    {R : Type w} [Field R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (outerBase innerTerm τ : ℝ) (q a b c d k : ℕ)
    (houterBase : 0 < outerBase) (hinnerTerm : 0 < innerTerm)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hstride : 0 < cwSquareStride a b c d) (hd : 0 < d) (hk : 0 < k)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1)))
    [Nonempty (CWSquareOuterSurvivor H a b c d k B seed)]
    (houterCopies : outerBase ^ k ≤
      (Fintype.card (CWSquareOuterSurvivor H a b c d k B seed) : ℝ))
    (inner : CyclicDegenerationCertificate K
      (cw112PartitionedTensor K q).realize τ)
    (hinnerPower : inner.power = d * k)
    (hinner : innerTerm ≤ inner.term) :
    cwSquareTauValueLimitLowerTerm outerBase innerTerm τ q a b c d ≤
      (cwSquareTauValueCertificateOfCyclicInner
        K H τ q a b c d k hq hordinary hd hk B hB seed inner hinnerPower).term τ := by
  rw [← cwSquareTauValueFiniteLowerTerm_eq_limit
    outerBase innerTerm τ q a b c d k houterBase hinnerTerm hq hstride hk]
  exact cwSquareTauValueFiniteLowerTerm_le_certificate
    K H outerBase innerTerm τ q a b c d k houterBase.le hinnerTerm.le
      hq hordinary hd hk B hB seed houterCopies inner hinnerPower hinner

end

end AlgebraicComplexity.Examples
