/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithMixedPowerRate
import AlgebraicComplexity.Examples.CoppersmithWinogradRectangularBound

/-!
# Coppersmith 1997: `α > 0.294`

This module is stage 3, the last, of [Cop97].  Stages 1 and 2
(`Examples/CoppersmithMixedPower{Type,Hashing,Rate}.lean`) produced the master scalar inequality

```text
cwMixedEntropyBase … / Φ · A ^ ω(1,1,κ) ≤ R,
A = q₇^{b₇} q₆^{b₆},  C = q₇^{a₇} q₆^{a₆},  R = (q₇+2)^{T₇} (q₆+2)^{T₆},  A^κ ≤ C,
```

for *any* geometric envelope `Φ` of the mixed competitor count.  This module supplies the
envelope, Coppersmith's four-parameter selection, and the endpoint.

## The envelope, and why the leg is not chosen by a Schur comparison

`cwMixedTypedFiberBound` is a **maximum over legs of a product** of the two halves'
`cwRectLegTypedFiber` values, so an envelope must dominate both the `x`-leg product and the
`y`-leg product.  `Examples/CoppersmithWinogradRectangularBound.lean` chooses the leg first, by
the Schur comparisons `cwRectLegTypedFiber_X_le_Y` (`b ≤ a`, `2e ≤ b`, `e ≤ f`) and
`cwRectLegTypedFiber_Y_le_X` (`a ≤ b`, `2e ≤ b`, `f ≤ e`), and only then builds the envelope.

**Neither hypothesis set holds at Coppersmith's parameters, on either half.**  On the `q = 7`
half `(a,b,e,f) = (2(u-s), 7u, s, 2u)`, so `b ≤ a` fails badly (`7u ≤ 2(u-s)`) and `f ≤ e` fails
badly (`2u ≤ s`); the same on the `q = 6` half.  The roadmap's expectation that "at Coppersmith's
parameters both halves give the `y` leg" is wrong, and so is the opposite guess: the two halves
select *different* legs (`x` on the `q = 7` half, `y` on the `q = 6` half), and it is only the
*product* over the two halves that has a winner.  That is exactly the content of the paper's
p. 45 sentence "We have chosen `a`, `b`, `s`, `t` to make the number of `y`-blocks approximately
equal to the number of `x`-blocks": at the true optimum the two products are *equal*, and the
four-parameter selection is precisely what balances them.

So the leg comparison is done here at the level of the envelopes, once, and multiplicatively:

* `cwRectLegTypedFiber_scaled_le_sharpX` and `cwRectLegTypedFiber_scaled_le_sharpY` are the two
  loss-free single-leg envelopes, *without* any leg-selection hypothesis (the hypotheses in
  `cwRectTypedFiberBound_scaled_le_sharp{,X}` are used only to collapse the maximum, which we
  cannot do here);
* `cwRectSharpFiberGrowth_mul_le_sharpX_mul` compares the two products through the two proved
  cancellations `E/Φ_x = ternaryEntropyBase` and `E/Φ_y = ternaryEntropyBase`, so the comparison
  becomes an inequality between the numbers of `x`-blocks and of `y`-blocks;
* `cwMixedTypedFiberBound_scaled_le_sharpX` then dominates the maximum by the `x`-leg envelope.

## Coppersmith's four-parameter selection, and the rational instance

`coppersmithLeftType u s = cwRectType (2(u-s)) (7u) s (2u)` and
`coppersmithRightType v t = cwRectType (v-2t) (3v) t v` (stage 1).  The continuous optimum of

```text
κ(u,s,v,t) = (2(u-s) log 7 + (v-2t) log 6) / (7u log 7 + 3v log 6)
```

subject to `#y-blocks ≥ #x-blocks` is `0.294628906…` at `(s/u, v/u, t/u) ≈ (0.02031, 1.28496,
0.01865)`, reproducing [Cop97, Theorem 1]'s `0.29462…` to six digits.  It is irrational, which is
why stage 2 left `κ` a parameter.  This module runs the *rational* instance

```text
u = 21,  s = 1,  v = 47,  t = 1,   κ = 5/17 = 0.294117…,
```

i.e. `(a₇,b₇,e₇,f₇) = (40, 147, 1, 42)` and `(a₆,b₆,e₆,f₆) = (45, 141, 1, 47)`, giving

```text
A = 7^147 · 6^141,   C = 7^40 · 6^45,   R = 9^378 · 8^376.
```

`5/17` is the simplest rational in the admissible window `(0.294, 0.294628906)`; the aspect-ratio
hypothesis `A^κ ≤ C` becomes the exact integer comparison `A^5 ≤ C^17` (`cop97_aspect_le`), so no
logarithm enclosure is used anywhere in this module.

## The near-equality `R ≤ N · M^{2+ε}` is an exact identity

[Cop97, §3, p. 43] observes that `C_q` "uses `q+2` multiplications ... The number of
`x`-variables is also `q+2`.  This agreement is necessary to achieve the near equality between
the number of operations and the number of `x`-variables in the larger algorithm."  Formalized,
that remark is not a `1+o(1)` estimate at all but the *exact* identity

```text
ternaryEntropyBase (2u) (14u) (2u) · (7^{7u})^2 = 9^{18u},
ternaryEntropyBase v (6v) v · (6^{3v})^2 = 8^{8v},
```

between the entropy base of the `x`-leg marginal (the growth rate of the number of `x`-blocks)
and the number of multiplications: `cop97_entropy_div_growth`.  Since
`cwMixedEntropyBase / Φ_x` is exactly that product of `x`-marginal entropy bases
(`cwRectSharpGrowthX_eq_ternaryEntropyBase`), the master inequality collapses to
`A^{ω(1,1,κ)} ≤ A^2`, with **no** `ε` and no subexponential slack:  the `ε` of the paper is the
Stirling loss that the Huang--Pan schedule has already absorbed.  This is why *any* mixture ratio
`a : b` is admissible, and it is the whole of item (3) of the stage-2 plan.

## Main results

* `cwRectLegTypedFiber_scaled_le_sharpX`, `cwRectLegTypedFiber_scaled_le_sharpY` --
  hypothesis-free loss-free single-leg envelopes;
* `cwRectSharpFiberGrowth_mul_le_sharpX_mul`, `cwMixedTypedFiberBound_scaled_le_sharpX` -- the
  mixed envelope;
* `cop97_marginal_le`, `cop97_left_identity`, `cop97_right_identity`, `cop97_aspect_le` -- the
  four exact integer certificates of the instance;
* `cop97_rectangularOmega_le_two`, `cop97_rectangularOmega_eq_two` -- `ω(1, 1, 5/17) = 2`;
* `coppersmith1997_rectangularAlpha_ge` -- `5/17 ≤ α(K)`;
* `coppersmith1997_alpha_gt` -- **[Cop97, Theorem 1]**, `α(K) > 0.294`.

## References

* [Cop97] D. Coppersmith, *Rectangular matrix multiplication revisited*, J. Complexity **13**
  (1997), 42--49; Sections 3--5 and Theorem 1 (p. 48).
* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299; Sections 5--7.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor Growth

universe u

/-! ## Loss-free single-leg competitor envelopes

`cwRectTypedFiberBound_scaled_le_sharp` and `cwRectTypedFiberBound_scaled_le_sharpX` bound the
*maximum* over legs, and their leg hypotheses serve only to collapse that maximum.  The mixed
construction cannot collapse a maximum one half at a time, so it needs the two underlying
estimates on their own. -/

/-- **The `x`-leg competitor envelope, with no leg-selection hypothesis.**  Along the schedule
`(a,b,e,f) ↦ (aN, bN, eN, fN)` each of the three binomial coefficients of
`cwRectLegTypedFiber … .X` is dominated exactly by the `N`-th power of a two-letter entropy
base. -/
theorem cwRectLegTypedFiber_scaled_le_sharpX {a b e f : ℕ} (ha : 0 < a) (hb : 0 < b)
    (he : 0 < e) (N : ℕ) :
    ((cwRectLegTypedFiber (a * N) (b * N) (e * N) (f * N) .X : ℕ) : ℝ) ≤
      cwRectSharpFiberGrowthX a b e ^ N := by
  have hb1 : ((Nat.choose (a * N + 2 * (e * N)) (a * N) : ℕ) : ℝ) ≤
      Analysis.binomialEntropyBase a (2 * e) ^ N := by
    have h := Analysis.choose_scaled_le_binomialEntropyBase_pow (p := a) (m := 2 * e) ha
      (by omega) N
    rwa [show (a + 2 * e) * N = a * N + 2 * (e * N) from by ring] at h
  have hb2 : ((Nat.choose (2 * (e * N)) (e * N) : ℕ) : ℝ) ≤
      Analysis.binomialEntropyBase e e ^ N := by
    have h := Analysis.choose_scaled_le_binomialEntropyBase_pow (p := e) (m := e) he he N
    rwa [show (e + e) * N = 2 * (e * N) from by ring] at h
  have hb3 : ((Nat.choose (2 * (b * N)) (b * N) : ℕ) : ℝ) ≤
      Analysis.binomialEntropyBase b b ^ N := by
    have h := Analysis.choose_scaled_le_binomialEntropyBase_pow (p := b) (m := b) hb hb N
    rwa [show (b + b) * N = 2 * (b * N) from by ring] at h
  have hval : cwRectLegTypedFiber (a * N) (b * N) (e * N) (f * N) .X =
      Nat.choose (a * N + 2 * (e * N)) (a * N) * Nat.choose (2 * (e * N)) (e * N) *
        Nat.choose (2 * (b * N)) (b * N) := rfl
  rw [hval]
  push_cast
  have hnn2 : (0 : ℝ) ≤ ((Nat.choose (2 * (e * N)) (e * N) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnn3 : (0 : ℝ) ≤ ((Nat.choose (2 * (b * N)) (b * N) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hE1 : (0 : ℝ) ≤ Analysis.binomialEntropyBase a (2 * e) ^ N :=
    pow_nonneg (Analysis.binomialEntropyBase_pos ha (by omega)).le N
  have hE2 : (0 : ℝ) ≤ Analysis.binomialEntropyBase e e ^ N :=
    pow_nonneg (Analysis.binomialEntropyBase_pos he he).le N
  unfold cwRectSharpFiberGrowthX
  rw [mul_pow, mul_pow]
  exact mul_le_mul (mul_le_mul hb1 hb2 hnn2 hE1) hb3 hnn3 (mul_nonneg hE1 hE2)

/-- **The `y`-leg competitor envelope, with no leg-selection hypothesis.** -/
theorem cwRectLegTypedFiber_scaled_le_sharpY {a b e f : ℕ} (ha : 0 < a) (hb : 0 < b)
    (he : 0 < e) (hf : 0 < f) (N : ℕ) :
    ((cwRectLegTypedFiber (a * N) (b * N) (e * N) (f * N) .Y : ℕ) : ℝ) ≤
      cwRectSharpFiberGrowth a b e f ^ N := by
  have hb1 : ((Nat.choose (b * N + e * N + f * N) (b * N) : ℕ) : ℝ) ≤
      Analysis.binomialEntropyBase b (e + f) ^ N := by
    have h := Analysis.choose_scaled_le_binomialEntropyBase_pow (p := b) (m := e + f) hb
      (by omega) N
    rwa [show (b + (e + f)) * N = b * N + e * N + f * N from by ring] at h
  have hb2 : ((Nat.choose (e * N + f * N) (e * N) : ℕ) : ℝ) ≤
      Analysis.binomialEntropyBase e f ^ N := by
    have h := Analysis.choose_scaled_le_binomialEntropyBase_pow (p := e) (m := f) he hf N
    rwa [show (e + f) * N = e * N + f * N from by ring] at h
  have hb3 : ((Nat.choose (a * N + b * N) (a * N) : ℕ) : ℝ) ≤
      Analysis.binomialEntropyBase a b ^ N := by
    have h := Analysis.choose_scaled_le_binomialEntropyBase_pow (p := a) (m := b) ha hb N
    rwa [show (a + b) * N = a * N + b * N from by ring] at h
  have hval : cwRectLegTypedFiber (a * N) (b * N) (e * N) (f * N) .Y =
      Nat.choose (b * N + e * N + f * N) (b * N) * Nat.choose (e * N + f * N) (e * N) *
        Nat.choose (a * N + b * N) (a * N) := rfl
  rw [hval]
  push_cast
  have hnn2 : (0 : ℝ) ≤ ((Nat.choose (e * N + f * N) (e * N) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnn3 : (0 : ℝ) ≤ ((Nat.choose (a * N + b * N) (a * N) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hE1 : (0 : ℝ) ≤ Analysis.binomialEntropyBase b (e + f) ^ N :=
    pow_nonneg (Analysis.binomialEntropyBase_pos hb (by omega)).le N
  have hE2 : (0 : ℝ) ≤ Analysis.binomialEntropyBase e f ^ N :=
    pow_nonneg (Analysis.binomialEntropyBase_pos he hf).le N
  unfold cwRectSharpFiberGrowth
  rw [mul_pow, mul_pow]
  exact mul_le_mul (mul_le_mul hb1 hb2 hnn2 hE1) hb3 hnn3 (mul_nonneg hE1 hE2)

/-! ## The mixed envelope -/

/-- Positivity of the ternary entropy base, read off the quotient-of-powers form. -/
theorem ternaryEntropyBase_pos {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < WordType.ternaryEntropyBase a b c := by
  rw [ternaryEntropyBase_eq_pow_div ha hb hc]
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hTR : (0 : ℝ) < ((a + b + c : ℕ) : ℝ) := by
    have : 0 < a + b + c := by omega
    exact_mod_cast this
  positivity

/-- **The two-sided leg comparison, done multiplicatively.**  The `y`-leg envelope product is
dominated by the `x`-leg envelope product exactly when the product of the two `x`-marginal
entropy bases -- the growth rate of the number of `x`-blocks -- is at most the product of the two
`y`-marginal ones.  Both halves cancel against the same six-fold multinomial base
`cwRectEntropyBase`, so no leg has to be selected on either half separately. -/
theorem cwRectSharpFiberGrowth_mul_le_sharpX_mul
    {a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ}
    (ha₇ : 0 < a₇) (hb₇ : 0 < b₇) (he₇ : 0 < e₇) (hf₇ : 0 < f₇)
    (ha₆ : 0 < a₆) (hb₆ : 0 < b₆) (he₆ : 0 < e₆) (hf₆ : 0 < f₆)
    (h : WordType.ternaryEntropyBase f₇ (2 * b₇) (a₇ + 2 * e₇) *
          WordType.ternaryEntropyBase f₆ (2 * b₆) (a₆ + 2 * e₆) ≤
        WordType.ternaryEntropyBase e₇ (a₇ + b₇) (b₇ + e₇ + f₇) *
          WordType.ternaryEntropyBase e₆ (a₆ + b₆) (b₆ + e₆ + f₆)) :
    cwRectSharpFiberGrowth a₇ b₇ e₇ f₇ * cwRectSharpFiberGrowth a₆ b₆ e₆ f₆ ≤
      cwRectSharpFiberGrowthX a₇ b₇ e₇ * cwRectSharpFiberGrowthX a₆ b₆ e₆ := by
  have hX₇ := cwRectSharpFiberGrowthX_pos ha₇ hb₇ he₇
  have hX₆ := cwRectSharpFiberGrowthX_pos ha₆ hb₆ he₆
  have hY₇ := cwRectSharpFiberGrowth_pos ha₇ hb₇ he₇ hf₇
  have hY₆ := cwRectSharpFiberGrowth_pos ha₆ hb₆ he₆ hf₆
  have keyX₇ : cwRectEntropyBase a₇ b₇ e₇ f₇ =
      WordType.ternaryEntropyBase f₇ (2 * b₇) (a₇ + 2 * e₇) *
        cwRectSharpFiberGrowthX a₇ b₇ e₇ :=
    (div_eq_iff hX₇.ne').mp (cwRectSharpGrowthX_eq_ternaryEntropyBase ha₇ hb₇ he₇ hf₇)
  have keyX₆ : cwRectEntropyBase a₆ b₆ e₆ f₆ =
      WordType.ternaryEntropyBase f₆ (2 * b₆) (a₆ + 2 * e₆) *
        cwRectSharpFiberGrowthX a₆ b₆ e₆ :=
    (div_eq_iff hX₆.ne').mp (cwRectSharpGrowthX_eq_ternaryEntropyBase ha₆ hb₆ he₆ hf₆)
  have keyY₇ : cwRectEntropyBase a₇ b₇ e₇ f₇ =
      WordType.ternaryEntropyBase e₇ (a₇ + b₇) (b₇ + e₇ + f₇) *
        cwRectSharpFiberGrowth a₇ b₇ e₇ f₇ :=
    (div_eq_iff hY₇.ne').mp (cwRectSharpGrowth_eq_ternaryEntropyBase ha₇ hb₇ he₇ hf₇)
  have keyY₆ : cwRectEntropyBase a₆ b₆ e₆ f₆ =
      WordType.ternaryEntropyBase e₆ (a₆ + b₆) (b₆ + e₆ + f₆) *
        cwRectSharpFiberGrowth a₆ b₆ e₆ f₆ :=
    (div_eq_iff hY₆.ne').mp (cwRectSharpGrowth_eq_ternaryEntropyBase ha₆ hb₆ he₆ hf₆)
  have hTBY : (0 : ℝ) < WordType.ternaryEntropyBase e₇ (a₇ + b₇) (b₇ + e₇ + f₇) *
      WordType.ternaryEntropyBase e₆ (a₆ + b₆) (b₆ + e₆ + f₆) :=
    mul_pos (ternaryEntropyBase_pos he₇ (by omega) (by omega))
      (ternaryEntropyBase_pos he₆ (by omega) (by omega))
  refine le_of_mul_le_mul_right ?_ hTBY
  calc cwRectSharpFiberGrowth a₇ b₇ e₇ f₇ * cwRectSharpFiberGrowth a₆ b₆ e₆ f₆ *
        (WordType.ternaryEntropyBase e₇ (a₇ + b₇) (b₇ + e₇ + f₇) *
          WordType.ternaryEntropyBase e₆ (a₆ + b₆) (b₆ + e₆ + f₆))
      = cwRectEntropyBase a₇ b₇ e₇ f₇ * cwRectEntropyBase a₆ b₆ e₆ f₆ := by
        rw [keyY₇, keyY₆]; ring
    _ = cwRectSharpFiberGrowthX a₇ b₇ e₇ * cwRectSharpFiberGrowthX a₆ b₆ e₆ *
          (WordType.ternaryEntropyBase f₇ (2 * b₇) (a₇ + 2 * e₇) *
            WordType.ternaryEntropyBase f₆ (2 * b₆) (a₆ + 2 * e₆)) := by
        rw [keyX₇, keyX₆]; ring
    _ ≤ cwRectSharpFiberGrowthX a₇ b₇ e₇ * cwRectSharpFiberGrowthX a₆ b₆ e₆ *
          (WordType.ternaryEntropyBase e₇ (a₇ + b₇) (b₇ + e₇ + f₇) *
            WordType.ternaryEntropyBase e₆ (a₆ + b₆) (b₆ + e₆ + f₆)) :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-- **The mixed competitor envelope.**  `cwMixedTypedFiberBound` is a maximum over legs of a
product; both branches are dominated by the `x`-leg envelope product, the `y`-branch through
`cwRectSharpFiberGrowth_mul_le_sharpX_mul`. -/
theorem cwMixedTypedFiberBound_scaled_le_sharpX
    {a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ}
    (ha₇ : 0 < a₇) (hb₇ : 0 < b₇) (he₇ : 0 < e₇) (hf₇ : 0 < f₇)
    (ha₆ : 0 < a₆) (hb₆ : 0 < b₆) (he₆ : 0 < e₆) (hf₆ : 0 < f₆)
    (hYX : cwRectSharpFiberGrowth a₇ b₇ e₇ f₇ * cwRectSharpFiberGrowth a₆ b₆ e₆ f₆ ≤
      cwRectSharpFiberGrowthX a₇ b₇ e₇ * cwRectSharpFiberGrowthX a₆ b₆ e₆)
    (N : ℕ) :
    ((cwMixedTypedFiberBound (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N)
        (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N) : ℕ) : ℝ) ≤
      (cwRectSharpFiberGrowthX a₇ b₇ e₇ * cwRectSharpFiberGrowthX a₆ b₆ e₆) ^ N := by
  have hX₇ := cwRectSharpFiberGrowthX_pos ha₇ hb₇ he₇
  have hX₆ := cwRectSharpFiberGrowthX_pos ha₆ hb₆ he₆
  have hY₇ := cwRectSharpFiberGrowth_pos ha₇ hb₇ he₇ hf₇
  have hY₆ := cwRectSharpFiberGrowth_pos ha₆ hb₆ he₆ hf₆
  unfold cwMixedTypedFiberBound
  rw [Nat.cast_max]
  refine max_le ?_ ?_
  · push_cast
    rw [mul_pow]
    exact mul_le_mul (cwRectLegTypedFiber_scaled_le_sharpX ha₇ hb₇ he₇ N)
      (cwRectLegTypedFiber_scaled_le_sharpX ha₆ hb₆ he₆ N) (Nat.cast_nonneg _)
      (pow_nonneg hX₇.le N)
  · have hstep : ((cwRectLegTypedFiber (a₇ * N) (b₇ * N) (e₇ * N) (f₇ * N) .Y : ℕ) : ℝ) *
        ((cwRectLegTypedFiber (a₆ * N) (b₆ * N) (e₆ * N) (f₆ * N) .Y : ℕ) : ℝ) ≤
        (cwRectSharpFiberGrowth a₇ b₇ e₇ f₇ * cwRectSharpFiberGrowth a₆ b₆ e₆ f₆) ^ N := by
      rw [mul_pow]
      exact mul_le_mul (cwRectLegTypedFiber_scaled_le_sharpY ha₇ hb₇ he₇ hf₇ N)
        (cwRectLegTypedFiber_scaled_le_sharpY ha₆ hb₆ he₆ hf₆ N) (Nat.cast_nonneg _)
        (pow_nonneg hY₇.le N)
    push_cast
    exact hstep.trans (pow_le_pow_left₀ (by positivity) hYX N)

/-! ## Coppersmith's four-parameter selection at `(u, s, v, t) = (21, 1, 47, 1)`

`coppersmithLeftType 21 1` and `coppersmithRightType 47 1` are the paper's retained profiles;
the two `rfl`-level identifications below record which `cwRectType` they are. -/

/-- The `q = 7` half of the instance: `a = 2u = 42`, `s = 1`. -/
theorem cop97_leftType : coppersmithLeftType 21 1 = cwRectType 40 147 1 42 := by
  norm_num [coppersmithLeftType]

/-- The `q = 6` half of the instance: `b = v = 47`, `t = 1`. -/
theorem cop97_rightType : coppersmithRightType 47 1 = cwRectType 45 141 1 47 := by
  norm_num [coppersmithRightType]

/-! ### The four exact integer certificates

Every numeric fact of the instance is an exact comparison of natural numbers.  No logarithm
enclosure, no floating-point evaluation and no `native_decide` enters the argument. -/

section Certificates

set_option exponentiation.threshold 400

/-- **The number of `x`-blocks is at most the number of `y`-blocks**, in the form the envelope
comparison needs: the `x`-marginals are `(42, 294, 42)` on the left and `(47, 282, 47)` on the
right, the `y`-marginals are `(1, 187, 190)` and `(1, 186, 189)`, and the inequality between the
two products of falling factorial denominators is [Cop97, p. 45]'s balancing condition. -/
theorem cop97_marginal_le :
    (1 ^ 1 * 187 ^ 187 * 190 ^ 190) * (1 ^ 1 * 186 ^ 186 * 189 ^ 189) ≤
      (42 ^ 42 * 294 ^ 294 * 42 ^ 42) * (47 ^ 47 * 282 ^ 282 * 47 ^ 47) := by
  norm_num

/-- **[Cop97, §3] on the `q = 7` half, exactly**: the entropy base of the `x`-marginal times
`(7^{147})^2` is `9^{378}`, the number of multiplications.  Equivalently
`378^378 · 7^294 = 9^378 · 42^42 · 294^294 · 42^42`. -/
theorem cop97_left_identity :
    (42 + 294 + 42) ^ (42 + 294 + 42) * 7 ^ 294 =
      9 ^ (42 + 294 + 42) * (42 ^ 42 * 294 ^ 294 * 42 ^ 42) := by
  norm_num

/-- **[Cop97, §3] on the `q = 6` half, exactly**: `376^376 · 6^282 = 8^376 · 47^47 · 282^282 ·
47^47`. -/
theorem cop97_right_identity :
    (47 + 282 + 47) ^ (47 + 282 + 47) * 6 ^ 282 =
      8 ^ (47 + 282 + 47) * (47 ^ 47 * 282 ^ 282 * 47 ^ 47) := by
  norm_num

/-- **The aspect ratio `κ = 5/17` is admissible**: `A^5 ≤ C^17` with `A = 7^147 · 6^141` and
`C = 7^40 · 6^45`, i.e. `7^55 ≤ 6^60`. -/
theorem cop97_aspect_le : (7 ^ 147 * 6 ^ 141 : ℕ) ^ 5 ≤ (7 ^ 40 * 6 ^ 45 : ℕ) ^ 17 := by
  norm_num

end Certificates

/-! ### The envelope at the instance -/

private theorem div_mul_div_le_div_mul_div {A B x y w z : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 < x) (hy : 0 < y) (hw : 0 < w) (hz : 0 < z)
    (h : w * z ≤ x * y) : A / x * (B / y) ≤ A / w * (B / z) := by
  rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff₀ (mul_pos hx hy) (mul_pos hw hz)]
  exact mul_le_mul_of_nonneg_left h (mul_nonneg hA hB)

/-! Numerals are kept out of the next two proofs deliberately.  At the sizes of the instance a
`simp`, `push_cast` or `ring` pass that meets a numeral power evaluates it, and the resulting
literal no longer matches the surrounding terms; the two helpers therefore do the algebra with
free variables, and the numerals appear only inside the four `norm_num` certificates. -/

/-- `T^T/(a^a b^b c^c) · q^k = R^T` from the corresponding exact identity of naturals. -/
private theorem ternaryEntropyBase_mul_pow_eq {a b c q R k : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hid : (a + b + c) ^ (a + b + c) * q ^ k = R ^ (a + b + c) * (a ^ a * b ^ b * c ^ c)) :
    WordType.ternaryEntropyBase a b c * ((q : ℕ) : ℝ) ^ k = ((R : ℕ) : ℝ) ^ (a + b + c) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  rw [ternaryEntropyBase_eq_pow_div ha hb hc, div_mul_eq_mul_div,
    div_eq_iff (by positivity : ((a : ℝ) ^ a * (b : ℝ) ^ b * (c : ℝ) ^ c) ≠ 0)]
  exact_mod_cast hid

/-- Two ternary entropy bases of equal total mass compare, multiplicatively, by the reverse
comparison of the products of their `x^x` denominators. -/
private theorem ternaryEntropyBase_mul_le_mul {a b c a' b' c' d e f d' e' f' : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ha' : 0 < a') (hb' : 0 < b') (hc' : 0 < c')
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (hd' : 0 < d') (he' : 0 < e') (hf' : 0 < f')
    (hs : a + b + c = a' + b' + c') (ht : d + e + f = d' + e' + f')
    (h : (a' ^ a' * b' ^ b' * c' ^ c') * (d' ^ d' * e' ^ e' * f' ^ f') ≤
      (a ^ a * b ^ b * c ^ c) * (d ^ d * e ^ e * f ^ f)) :
    WordType.ternaryEntropyBase a b c * WordType.ternaryEntropyBase d e f ≤
      WordType.ternaryEntropyBase a' b' c' * WordType.ternaryEntropyBase d' e' f' := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have ha'R : (0 : ℝ) < (a' : ℝ) := by exact_mod_cast ha'
  have hb'R : (0 : ℝ) < (b' : ℝ) := by exact_mod_cast hb'
  have hc'R : (0 : ℝ) < (c' : ℝ) := by exact_mod_cast hc'
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hfR : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have hd'R : (0 : ℝ) < (d' : ℝ) := by exact_mod_cast hd'
  have he'R : (0 : ℝ) < (e' : ℝ) := by exact_mod_cast he'
  have hf'R : (0 : ℝ) < (f' : ℝ) := by exact_mod_cast hf'
  have hkey : ((a' : ℝ) ^ a' * (b' : ℝ) ^ b' * (c' : ℝ) ^ c') *
      ((d' : ℝ) ^ d' * (e' : ℝ) ^ e' * (f' : ℝ) ^ f') ≤
      ((a : ℝ) ^ a * (b : ℝ) ^ b * (c : ℝ) ^ c) *
        ((d : ℝ) ^ d * (e : ℝ) ^ e * (f : ℝ) ^ f) := by
    exact_mod_cast h
  rw [ternaryEntropyBase_eq_pow_div ha hb hc, ternaryEntropyBase_eq_pow_div hd he hf,
    ternaryEntropyBase_eq_pow_div ha' hb' hc', ternaryEntropyBase_eq_pow_div hd' he' hf',
    ← hs, ← ht]
  exact div_mul_div_le_div_mul_div (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) hkey

/-- The balancing condition of the instance, at the level of entropy bases. -/
theorem cop97_ternary_le :
    WordType.ternaryEntropyBase 42 294 42 * WordType.ternaryEntropyBase 47 282 47 ≤
      WordType.ternaryEntropyBase 1 187 190 * WordType.ternaryEntropyBase 1 186 189 :=
  ternaryEntropyBase_mul_le_mul (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) cop97_marginal_le

/-- The `y`-leg envelope product is dominated by the `x`-leg one at Coppersmith's instance. -/
theorem cop97_sharp_le :
    cwRectSharpFiberGrowth 40 147 1 42 * cwRectSharpFiberGrowth 45 141 1 47 ≤
      cwRectSharpFiberGrowthX 40 147 1 * cwRectSharpFiberGrowthX 45 141 1 :=
  cwRectSharpFiberGrowth_mul_le_sharpX_mul (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa using cop97_ternary_le)

/-- **The near-equality of [Cop97, §3], as an exact identity**: at Coppersmith's selection the
six-fold multinomial base divided by the `x`-leg envelope, times `A²`, is exactly the number of
multiplications `R`. -/
theorem cop97_entropy_div_growth :
    cwMixedEntropyBase 40 147 1 42 45 141 1 47 /
        (cwRectSharpFiberGrowthX 40 147 1 * cwRectSharpFiberGrowthX 45 141 1) *
      (((7 ^ 147 * 6 ^ 141 : ℕ) : ℝ)) ^ (2 : ℕ) = ((9 ^ 378 * 8 ^ 376 : ℕ) : ℝ) := by
  have hX₇ : (0 : ℝ) < cwRectSharpFiberGrowthX 40 147 1 :=
    cwRectSharpFiberGrowthX_pos (by norm_num) (by norm_num) (by norm_num)
  have hX₆ : (0 : ℝ) < cwRectSharpFiberGrowthX 45 141 1 :=
    cwRectSharpFiberGrowthX_pos (by norm_num) (by norm_num) (by norm_num)
  have hsplit : cwMixedEntropyBase 40 147 1 42 45 141 1 47 /
      (cwRectSharpFiberGrowthX 40 147 1 * cwRectSharpFiberGrowthX 45 141 1) =
      (cwRectEntropyBase 40 147 1 42 / cwRectSharpFiberGrowthX 40 147 1) *
        (cwRectEntropyBase 45 141 1 47 / cwRectSharpFiberGrowthX 45 141 1) := by
    rw [cwMixedEntropyBase, div_mul_div_comm]
  have h₇ : cwRectEntropyBase 40 147 1 42 / cwRectSharpFiberGrowthX 40 147 1 =
      WordType.ternaryEntropyBase 42 294 42 :=
    cwRectSharpGrowthX_eq_ternaryEntropyBase (p := 40) (m := 147) (u := 1) (v := 42)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₆ : cwRectEntropyBase 45 141 1 47 / cwRectSharpFiberGrowthX 45 141 1 =
      WordType.ternaryEntropyBase 47 282 47 :=
    cwRectSharpGrowthX_eq_ternaryEntropyBase (p := 45) (m := 141) (u := 1) (v := 47)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hTB₇ : WordType.ternaryEntropyBase 42 294 42 * ((7 : ℕ) : ℝ) ^ (294 : ℕ) =
      ((9 : ℕ) : ℝ) ^ (378 : ℕ) :=
    ternaryEntropyBase_mul_pow_eq (by norm_num) (by norm_num) (by norm_num) cop97_left_identity
  have hTB₆ : WordType.ternaryEntropyBase 47 282 47 * ((6 : ℕ) : ℝ) ^ (282 : ℕ) =
      ((8 : ℕ) : ℝ) ^ (376 : ℕ) :=
    ternaryEntropyBase_mul_pow_eq (by norm_num) (by norm_num) (by norm_num) cop97_right_identity
  have hAnat : (7 ^ 147 * 6 ^ 141 : ℕ) ^ 2 = 7 ^ 294 * 6 ^ 282 := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  have hcastA : (((7 ^ 147 * 6 ^ 141 : ℕ)) : ℝ) ^ (2 : ℕ) =
      ((7 : ℕ) : ℝ) ^ (294 : ℕ) * ((6 : ℕ) : ℝ) ^ (282 : ℕ) := by
    rw [← Nat.cast_pow, hAnat, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  have hcastR : ((9 ^ 378 * 8 ^ 376 : ℕ) : ℝ) =
      ((9 : ℕ) : ℝ) ^ (378 : ℕ) * ((8 : ℕ) : ℝ) ^ (376 : ℕ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  rw [hsplit, h₇, h₆, hcastA, hcastR]
  calc WordType.ternaryEntropyBase 42 294 42 * WordType.ternaryEntropyBase 47 282 47 *
        (((7 : ℕ) : ℝ) ^ (294 : ℕ) * ((6 : ℕ) : ℝ) ^ (282 : ℕ))
      = (WordType.ternaryEntropyBase 42 294 42 * ((7 : ℕ) : ℝ) ^ (294 : ℕ)) *
        (WordType.ternaryEntropyBase 47 282 47 * ((6 : ℕ) : ℝ) ^ (282 : ℕ)) :=
        mul_mul_mul_comm _ _ _ _
    _ = ((9 : ℕ) : ℝ) ^ (378 : ℕ) * ((8 : ℕ) : ℝ) ^ (376 : ℕ) := by rw [hTB₇, hTB₆]

/-! ## The endpoint -/

section Endpoint

variable (K : Type u) [Field K]

/-- **`ω(1, 1, 5/17) ≤ 2`.**  The master inequality of stage 2, run at Coppersmith's selection
with the `x`-leg envelope, becomes `A^{ω} ≤ A^2` because the near-equality of [Cop97, §3] is an
exact identity. -/
theorem cop97_rectangularOmega_le_two : rectangularOmega K (5 / 17) ≤ 2 := by
  have hX₇ : (0 : ℝ) < cwRectSharpFiberGrowthX 40 147 1 :=
    cwRectSharpFiberGrowthX_pos (by norm_num) (by norm_num) (by norm_num)
  have hX₆ : (0 : ℝ) < cwRectSharpFiberGrowthX 45 141 1 :=
    cwRectSharpFiberGrowthX_pos (by norm_num) (by norm_num) (by norm_num)
  have hone₇ : (1 : ℝ) ≤ cwRectSharpFiberGrowthX 40 147 1 :=
    one_le_cwRectSharpFiberGrowthX (by norm_num) (by norm_num) (by norm_num)
  have hone₆ : (1 : ℝ) ≤ cwRectSharpFiberGrowthX 45 141 1 :=
    one_le_cwRectSharpFiberGrowthX (by norm_num) (by norm_num) (by norm_num)
  have hΦ : (1 : ℝ) ≤ cwRectSharpFiberGrowthX 40 147 1 * cwRectSharpFiberGrowthX 45 141 1 := by
    nlinarith
  -- the aspect-ratio hypothesis, from the exact integer comparison `A^5 ≤ C^17`
  have hAR : (0 : ℝ) < ((7 ^ 147 * 6 ^ 141 : ℕ) : ℝ) := by positivity
  have hCR : (0 : ℝ) ≤ ((7 ^ 40 * 6 ^ 45 : ℕ) : ℝ) := by positivity
  have hmid : (((7 ^ 147 * 6 ^ 141 : ℕ)) : ℝ) ^ ((5 : ℝ) / 17) ≤
      (((7 ^ 40 * 6 ^ 45 : ℕ)) : ℝ) := by
    refine le_of_pow_le_pow_left₀ (n := 17) (by norm_num) hCR ?_
    rw [← Real.rpow_natCast ((((7 ^ 147 * 6 ^ 141 : ℕ)) : ℝ) ^ ((5 : ℝ) / 17)) 17,
      ← Real.rpow_mul hAR.le,
      show ((5 : ℝ) / 17 * ((17 : ℕ) : ℝ)) = ((5 : ℕ) : ℝ) from by push_cast; ring,
      Real.rpow_natCast]
    exact_mod_cast cop97_aspect_le
  have hAone : (1 : ℝ) < ((7 ^ 147 * 6 ^ 141 : ℕ) : ℝ) := by
    have h : (1 : ℕ) < 7 ^ 147 * 6 ^ 141 := by norm_num
    exact_mod_cast h
  have hmaster := cwMixed_master_inequality_of_fiberGrowth (K := K) (q₇ := 7) (q₆ := 6)
    (a₇ := 40) (b₇ := 147) (e₇ := 1) (f₇ := 42) (a₆ := 45) (b₆ := 141) (e₆ := 1) (f₆ := 47)
    (κ := (5 : ℝ) / 17)
    (Φ := cwRectSharpFiberGrowthX 40 147 1 * cwRectSharpFiberGrowthX 45 141 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmid hΦ
    (fun N ↦ cwMixedTypedFiberBound_scaled_le_sharpX (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) cop97_sharp_le N)
  have hGpos : (0 : ℝ) < cwMixedEntropyBase 40 147 1 42 45 141 1 47 /
      (cwRectSharpFiberGrowthX 40 147 1 * cwRectSharpFiberGrowthX 45 141 1) :=
    div_pos (cwMixedEntropyBase_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (mul_pos hX₇ hX₆)
  have hRHS : ((((7 + 2) ^ (40 + 2 * 147 + 2 * 1 + 42) *
        (6 + 2) ^ (45 + 2 * 141 + 2 * 1 + 47) : ℕ)) : ℝ) =
      cwMixedEntropyBase 40 147 1 42 45 141 1 47 /
          (cwRectSharpFiberGrowthX 40 147 1 * cwRectSharpFiberGrowthX 45 141 1) *
        (((7 ^ 147 * 6 ^ 141 : ℕ)) : ℝ) ^ (2 : ℕ) := by
    rw [cop97_entropy_div_growth]
  have hchain := hmaster.trans (le_of_eq hRHS)
  have hpow : (((7 ^ 147 * 6 ^ 141 : ℕ)) : ℝ) ^ (rectangularOmega K ((5 : ℝ) / 17)) ≤
      (((7 ^ 147 * 6 ^ 141 : ℕ)) : ℝ) ^ (((2 : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]
    exact le_of_mul_le_mul_left hchain hGpos
  have hfinal := (Real.rpow_le_rpow_left_iff hAone).mp hpow
  simpa using hfinal

/-- **`ω(1, 1, 5/17) = 2`**: the upper bound is Coppersmith's construction, the lower bound the
outer flattening. -/
theorem cop97_rectangularOmega_eq_two : rectangularOmega K (5 / 17) = 2 :=
  le_antisymm (cop97_rectangularOmega_le_two K) (two_le_rectangularOmega K _)

/-- **[Cop97, Theorem 1], lower-bound form**: `5/17 ≤ α(K)` over every field. -/
theorem coppersmith1997_rectangularAlpha_ge : (5 : ℝ) / 17 ≤ rectangularAlpha K :=
  le_csSup (bddAbove_setOf_rectangularOmega_eq_two K)
    ⟨by norm_num, cop97_rectangularOmega_eq_two K⟩

/-- **[Cop97, Theorem 1]**: `α(K) > 0.294` over every field.  The paper's optimum is
`0.29462…`; the rational instance `(u, s, v, t) = (21, 1, 47, 1)` certified here reaches
`5/17 = 0.294117…`. -/
theorem coppersmith1997_alpha_gt : (294 : ℝ) / 1000 < rectangularAlpha K :=
  lt_of_lt_of_le (by norm_num) (coppersmith1997_rectangularAlpha_ge K)

end Endpoint

end AlgebraicComplexity.Examples
