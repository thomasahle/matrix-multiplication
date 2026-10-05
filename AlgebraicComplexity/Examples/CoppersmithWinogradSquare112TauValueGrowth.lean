/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquare112TauValue
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareTauValueGrowth
import AlgebraicComplexity.MatrixMultiplication.TauValueSoundness

/-!
# Eventual modern `(112)` value certificates for the CW square

This file combines two independent, already semantic finite constructions at one common
proportional repetition:

* canonical outer CW-square hashing, whose survivor count attains every strict base below the
  five-coordinate marginal entropy base; and
* the modern cyclic `(1,1,2)` degeneration, whose normalized term attains the stable symmetric
  typed-leaf lower bound.

The result is one genuine `TauValueCertificate` for the original CW square.  Its lower bound is
the repetition-independent term from `CoppersmithWinogradSquareTauValueGrowth`.  Consequently a
strict comparison with the border-rank budget `(q+2)^2` immediately implies `omega < 3τ` through
the generic value calculus.  The file also records symbolic logarithm formulas for the symmetric
marginal entropy base and matrix-volume product, so downstream parameter clients need not unfold
the typed-leaf entropy again.

No numerical parameter choice occurs here.  In particular, the `q = 6` bounds `2.38` and
`2.375477` remain small downstream real-arithmetic certificates.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

noncomputable section

variable (K : Type u) [Field K]

/-- Stable lower term for the modern symmetric `(112)` extraction assembled inside the CW square.

`outerBase` controls the number of surviving outer blocks.  `innerCopyBase` controls the visible
marginal count in the cyclic 64-address inner extraction; its fully normalized contribution is
`cw112SymmetricLimitLowerTerm`. -/
noncomputable def cwSquareSymmetric112LimitLowerTerm
    (outerBase innerCopyBase τ : ℝ) (q a b c L G : ℕ)
    (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) : ℝ :=
  cwSquareTauValueLimitLowerTerm outerBase
    (cw112SymmetricLimitLowerTerm K innerCopyBase τ q L G hq hL hG)
    τ q a b c (cwSquareSymmetric112Multiplicity L G)

/-- The stable normalized value of the symmetric inner leaf is positive for a positive copy
base. -/
theorem cw112SymmetricLimitLowerTerm_pos
    {innerCopyBase : ℝ} (hinnerCopyBase : 0 < innerCopyBase)
    (τ : ℝ) (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    0 < cw112SymmetricLimitLowerTerm K innerCopyBase τ q L G hq hL hG := by
  let leaf := cw112SymmetricLeaf K q L G hq hL hG
  have hx := leaf.dimensionProduct_pos .X
  have hy := leaf.dimensionProduct_pos .Y
  have hz := leaf.dimensionProduct_pos .Z
  have hvolumeNat : 0 <
      leaf.dimensionProduct .X * leaf.dimensionProduct .Y * leaf.dimensionProduct .Z :=
    Nat.mul_pos (Nat.mul_pos hx hy) hz
  have hvolume : (0 : ℝ) <
      (leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
        leaf.dimensionProduct .Z : ℕ) := by
    exact_mod_cast hvolumeNat
  unfold cw112SymmetricLimitLowerTerm
  exact Real.rpow_pos_of_pos
    (mul_pos hinnerCopyBase (Real.rpow_pos_of_pos hvolume τ)) _

/-- Exact logarithm of the common visible marginal-entropy base of the symmetric `(112)` leaf.

Writing `s = 2(L+G)` and `D = s^3`, the formula is

```text
2 D log 2 + 2 L s^2 log (s/L) + 2 G s^2 log ((L+G)/G).
```

Proof sketch: the symmetric marginal has entropy `2 + H(mu,mu,1-2mu)` at mass `D`, where
`mu=L/s` and `1-2mu=G/(L+G)`.  Expanding `negMulLog x = x log(x⁻¹)` turns the two light atoms into
the coefficient `2 L s^2`, and the heavy atom into `2 G s^2`.  This symbolic form lets every
exact rational CW parameter client reuse the entropy calculation and retain only its genuinely
paper-specific directed logarithm bounds. -/
theorem log_cw112SymmetricMarginalEntropyBase
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    Real.log (cw112SymmetricMarginalEntropyBase K q L G hq hL hG) =
      (2 * (2 * (L + G)) ^ 3 : ℕ) * Real.log 2 +
        (2 * L * (2 * (L + G)) ^ 2 : ℕ) *
          Real.log (((2 * (L + G) : ℕ) : ℝ) / (L : ℝ)) +
        (2 * G * (2 * (L + G)) ^ 2 : ℕ) *
          Real.log (((L + G : ℕ) : ℝ) / (G : ℝ)) := by
  rw [cw112SymmetricMarginalEntropyBase_eq_exp, Real.log_exp]
  unfold cw112MuEntropyBits cw112Mu
  have hsumNat : 0 < L + G := Nat.add_pos_left hL G
  have hsum : (0 : ℝ) < L + G := by exact_mod_cast hsumNat
  have hLReal : (0 : ℝ) < L := by exact_mod_cast hL
  have hGReal : (0 : ℝ) < G := by exact_mod_cast hG
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hgrid :
      1 - 2 * ((L : ℝ) / (2 * (L + G) : ℕ)) = (G : ℝ) / (L + G) := by
    push_cast
    field_simp [hsum.ne']
    ring
  rw [hgrid]
  have hneg (x : ℝ) : Real.negMulLog x = x * Real.log x⁻¹ := by
    rw [Real.negMulLog_eq_neg, Real.log_inv]
    ring
  rw [hneg, hneg]
  simp only [inv_div]
  push_cast
  field_simp [hlogTwo, hsum.ne', hLReal.ne', hGReal.ne']
  ring

/-- Exact logarithm of the symmetric inner matrix-volume product.

Each leg dimension is `q^((4G+2L)(2(L+G))²)`, so the product of all three legs has the displayed
logarithm. -/
theorem log_cw112SymmetricDimensionVolume
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    Real.log
        (((cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .X *
          (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Y *
          (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Z : ℕ) : ℝ) =
      (((3 * ((2 * (L + G)) ^ 2) * (4 * G + 2 * L) : ℕ) : ℝ)) *
        Real.log q := by
  simp_rw [cw112SymmetricLeaf,
    cw112SymmetricPartitionRationalTypedLeaf_dimensionProduct]
  have hside : 0 < cw112FiniteLeafSquareSide q L G := by
    unfold cw112FiniteLeafSquareSide
    positivity
  norm_num only [Nat.cast_mul, Nat.cast_pow]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring

/-- Logarithm of the stable normalized symmetric inner lower term. -/
theorem log_cw112SymmetricLimitLowerTerm
    {innerCopyBase : ℝ} (hinnerCopyBase : 0 < innerCopyBase)
    (τ : ℝ) (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    Real.log (cw112SymmetricLimitLowerTerm
      K innerCopyBase τ q L G hq hL hG) =
      (((3 * (cw112SymmetricLeaf K q L G hq hL hG).profile.mass : ℕ) : ℝ)⁻¹) *
        (Real.log innerCopyBase +
          τ * Real.log
            (((cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .X *
              (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Y *
              (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Z : ℕ) : ℝ)) := by
  let leaf := cw112SymmetricLeaf K q L G hq hL hG
  have hx := leaf.dimensionProduct_pos .X
  have hy := leaf.dimensionProduct_pos .Y
  have hz := leaf.dimensionProduct_pos .Z
  have hvolumeNat : 0 <
      leaf.dimensionProduct .X * leaf.dimensionProduct .Y * leaf.dimensionProduct .Z :=
    Nat.mul_pos (Nat.mul_pos hx hy) hz
  have hvolume : (0 : ℝ) <
      (leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
        leaf.dimensionProduct .Z : ℕ) := by
    exact_mod_cast hvolumeNat
  unfold cw112SymmetricLimitLowerTerm
  rw [Real.log_rpow (mul_pos hinnerCopyBase
    (Real.rpow_pos_of_pos hvolume τ)),
    Real.log_mul hinnerCopyBase.ne' (Real.rpow_pos_of_pos hvolume τ).ne',
    Real.log_rpow hvolume]

/-- Every pair of strict outer and inner entropy bases produces an actual finite value certificate
for the original CW square whose term dominates the stable modern lower bound.

Proof sketch: choose a repetition beyond both eventual-growth cutoffs.  Positivity of each strict
base makes both selected survivor types nonempty.  Use the canonical inner cyclic degeneration and
the canonical outer affine hash in the relation-neutral stable assembly theorem.  Its exact power
normalization removes the common repetition parameter.
-/
theorem exists_cwSquareSymmetric112LimitCertificate
    (τ : ℝ) (q a b c L G : ℕ)
    (hq : 0 < q) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hL : 0 < L) (hG : 0 < G)
    {outerBase innerCopyBase : ℝ}
    (houterBase : 0 < outerBase)
    (houterLt : outerBase < cwSquareOuterEntropyBase a b c
      (cwSquareSymmetric112Multiplicity L G))
    (hinnerCopyBase : 0 < innerCopyBase)
    (hinnerLt : innerCopyBase <
      cw112SymmetricMarginalEntropyBase K q L G hq hL hG) :
    ∃ certificate : TauValueCertificate K (cwSquarePartitionedTensor K q).realize,
      cwSquareSymmetric112LimitLowerTerm K outerBase innerCopyBase τ
          q a b c L G hq hL hG ≤ certificate.term τ := by
  let d := cwSquareSymmetric112Multiplicity L G
  have hd : 0 < d := cwSquareSymmetric112Multiplicity_pos hL
  obtain ⟨outerCutoff, houterGrowth⟩ :=
    exists_eventually_cwSquareOuterSurvivorGrowth
      ha hb hc hd houterBase houterLt
  obtain ⟨innerCutoff, hinnerGrowth⟩ :=
    exists_eventually_cw112SymmetricLimitLowerTerm_le_certificate
      K τ q L G hq hL hG hinnerCopyBase hinnerLt
  let k := max outerCutoff innerCutoff
  have hkOuter : outerCutoff ≤ k := le_max_left _ _
  have hkInner : innerCutoff ≤ k := le_max_right _ _
  obtain ⟨hk, hstride, outerSeed, houterCopies⟩ :=
    houterGrowth k hkOuter
  obtain ⟨_hkInner, innerSeed, hinnerNonempty, hinnerTerm⟩ :=
    hinnerGrowth k hkInner
  let p := cwSquareOuterHashModulus a b c d k
  let H := cwSquareOuterHashEncoding a b c d k hstride hk
  let B := cwSquareOuterBuckets a b c d k
  let inner := cw112SymmetricCanonicalDegenerationValueCertificate
    K τ q L G k hq hL hG _hkInner innerSeed hinnerNonempty
  have hinnerPower : inner.power = d * k := by
    simpa only [inner, d] using
      cw112SymmetricCanonical_power_eq_squareMultiplicity_mul
        K τ q L G k hq hL hG _hkInner innerSeed hinnerNonempty
  have houterCardPos : 0 < Fintype.card
      (CWSquareOuterCanonicalSurvivor a b c d k hstride hk outerSeed) := by
    have hreal : (0 : ℝ) < Fintype.card
        (CWSquareOuterCanonicalSurvivor a b c d k hstride hk outerSeed) :=
      (pow_pos houterBase k).trans_le houterCopies
    exact_mod_cast hreal
  let houterNonempty : Nonempty
      (CWSquareOuterCanonicalSurvivor a b c d k hstride hk outerSeed) :=
    Fintype.card_pos_iff.mp houterCardPos
  letI : NeZero (2 : ZMod p) := neZero_two_zmod_of_three_le (by
    have hp := cwSquareOuterHashModulus_ge_five hstride hk
    simpa only [p] using (show 3 ≤ cwSquareOuterHashModulus a b c d k by omega))
  letI : Nonempty
      (CWSquareOuterSurvivor H a b c d k B outerSeed) := by
    simpa only [H, B, CWSquareOuterCanonicalSurvivor] using houterNonempty
  have hordinary : 0 < cwSquareStride a b c 0 := by
    unfold cwSquareStride
    positivity
  have hinnerStable : 0 <
      cw112SymmetricLimitLowerTerm K innerCopyBase τ q L G hq hL hG :=
    cw112SymmetricLimitLowerTerm_pos K hinnerCopyBase τ q L G hq hL hG
  let certificate := cwSquareTauValueCertificateOfCyclicInner
    K H τ q a b c d k hq hordinary hd hk B
      (by simpa only [B, p] using cwSquareOuterBuckets_threeAPFree a b c d k)
      outerSeed inner hinnerPower
  refine ⟨certificate, ?_⟩
  change cwSquareTauValueLimitLowerTerm outerBase
      (cw112SymmetricLimitLowerTerm K innerCopyBase τ q L G hq hL hG)
      τ q a b c d ≤ certificate.term τ
  exact cwSquareTauValueLimitLowerTerm_le_certificate
    K H outerBase
      (cw112SymmetricLimitLowerTerm K innerCopyBase τ q L G hq hL hG)
      τ q a b c d k houterBase hinnerStable hq hordinary hstride hd hk
      B (by simpa only [B, p] using cwSquareOuterBuckets_threeAPFree a b c d k)
      outerSeed (by
        simpa only [H, B, CWSquareOuterCanonicalSurvivor] using houterCopies)
      inner hinnerPower hinnerTerm

/-- **Modern CW-square value endpoint, conditional only on the final scalar inequality.**

If the stable lower term exceeds the square's constructive border-rank budget `(q+2)^2`, then
`omega < 3τ`.  All tensor restrictions, polynomial degenerations, entropy-rate limits, and
Schönhage soundness are discharged before this theorem; a numerical client only has to prove the
displayed strict real inequality.
-/
theorem cwSquareSymmetric112_omega_lt_three_mul
    (τ : ℝ) (q a b c L G : ℕ)
    (hq : 0 < q) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hL : 0 < L) (hG : 0 < G)
    {outerBase innerCopyBase : ℝ}
    (houterBase : 0 < outerBase)
    (houterLt : outerBase < cwSquareOuterEntropyBase a b c
      (cwSquareSymmetric112Multiplicity L G))
    (hinnerCopyBase : 0 < innerCopyBase)
    (hinnerLt : innerCopyBase <
      cw112SymmetricMarginalEntropyBase K q L G hq hL hG)
    (hstrict : (((q + 2) ^ 2 : ℕ) : ℝ) <
      cwSquareSymmetric112LimitLowerTerm K outerBase innerCopyBase τ
        q a b c L G hq hL hG) :
    omega K < 3 * τ := by
  obtain ⟨certificate, hterm⟩ :=
    exists_cwSquareSymmetric112LimitCertificate
      K τ q a b c L G hq ha hb hc hL hG
        houterBase houterLt hinnerCopyBase hinnerLt
  exact omega_lt_three_mul_of_borderRankLE K
    (cwSquarePartitionedTensor_borderRankLE K q) certificate
    (hstrict.trans_le hterm)

end

end AlgebraicComplexity.Examples
