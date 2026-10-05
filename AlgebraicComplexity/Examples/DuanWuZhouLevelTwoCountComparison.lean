/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompetitorRateBrick
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainFiberCount

set_option autoImplicit false

/-!
# `hcount`, the count-side rate comparison, in finite form

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoCompetitorRateBrick.lean`'s
`dwz63_cofinal_competitorBound_le_degree` takes

`hcount : ∀ N, |matchable α K| · ᾱ_p ^ N ≤ rslack N · r ^ N · d N`,  `r = ᾱ_p ᾱ_X / (ᾱ_Z K)`.

This module reduces it to two type-class estimates and nothing else, doing every exact step.

## The sharp degree *is* the `X`-leg fibre, plus one

`Examples/DuanWuZhouLevelTwoPlainFiberCount.lean`'s `card_dwz63PlainMarginalWords_eq` is the exact
identity `N_α′ = N_X · |fibre|`, so

`dwz63PlainSharpDegree K n t = N_α′ / N_X + 1 = |fibre| + 1`

(`dwz63PlainSharpDegree_eq_card_sourceWordLegFiber_add_one`).  Two consequences: the `+1` of
`dwz63SharpDegree` is the only slack in `d`, and the rate of `d` is the rate of the `X`-leg fibre,
`K ᾱ_α / ᾱ_X` — no separate estimate of `N_α′` and `N_X` is needed, and the committed
`card_sourceWordLegFiber_le_sharpDegree` is the same identity read the other way.

## The reduction

`dwz63_hcount_of_rate` derives `hcount` from

* `hupper : ∀ N, |matchable α K| ≤ su N · (ᾱ_α / ᾱ_Z) ^ N` — a **conditional type-class upper
  bound**, the loss-free direction of the method of types;
* `hlower : ∀ N, (K ᾱ_α / ᾱ_X) ^ N ≤ sl N · |fibre| ` — a **conditional type-class lower bound
  with subexponential slack** on the `X`-leg fibre;

with `su`, `sl` subexponential, and `rslack := su · sl`.  The algebra is the base identity
`ᾱ_p ᾱ_α / ᾱ_Z = (ᾱ_p ᾱ_X / (ᾱ_Z K)) · (K ᾱ_α / ᾱ_X)`, i.e. `r` is *defined* so that the two
estimates compose with **no loss beyond `su · sl`**.

## Status of the two inputs — neither is a missing brick

* `hupper` is the shape of `Analysis/StructuralZeroConditionalType.lean`'s
  `card_conditionalTypeClass_le_structuralZeroLoss_mul_exp_entropyDifference`, and of the loss-free
  `Combinatorics/TypeClassCounting.lean`'s `card_typeClass_le_exp_profileEntropy`.
* `hlower` is the shape of `Combinatorics/PushedProfileFiberGrowth.lean`'s
  `pushedTypeFiberEntropyBase_pow_le_loss_mul_card_typedFiber` (and its `_of_length_eq` variant in
  `Analysis/ConditionalLegFiberGrowth.lean`) — exactly `base ^ n ≤ loss · |typed fibre|` with a
  subexponential `loss`.  `Examples/DuanWuZhouLevelTwoPlainRate.lean`'s
  `dwz63_exp_entropyX_pow_le_loss_mul_dwz63PlainLegCount` is the same shape one level up, at the
  *leg* count rather than the fibre.

So the tree **has** both shapes; what is missing is the *instantiation* at
`dwz63PlainMarginalWords`' `X`-leg fibre, namely: identify
`PartitionHashEncoding.sourceWordLegFiber n (dwz63PlainMarginalWords K n t) .X x` with the typed
fibre of the pushforward along `cwSquareDegreeMap .X`, and evaluate its
`pushedTypeFiberEntropyBase` as `K ᾱ_α / ᾱ_X` from `GlobalArithmetic`'s atoms.  That is count-lane
bookkeeping of the same kind as `dwz63_exp_entropyX_pow_le_loss_mul_dwz63PlainLegCount`, not a new
mathematical input, and it is reported here rather than assumed.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`), §2.9 (`hashing.tex`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash CompatibleSplit
open scoped BigOperators

universe u v

/-! ## The sharp degree is the `X`-leg fibre plus one -/

/-- **`d = |fibre| + 1`, exactly.** -/
theorem dwz63PlainSharpDegree_eq_card_sourceWordLegFiber_add_one (K : Type u) [CommRing K]
    (c : Leg) (n t : ℕ) {x : PositiveWord (Fin 5) n} (hx : x ∈ dwz63PlainLegTargets c n t)
    (hpos : 0 < dwz63PlainLegCount c n t) :
    dwz63SharpDegree (dwz63PlainMarginalWords K n t).card (dwz63PlainLegCount c n t) =
      (PartitionHashEncoding.sourceWordLegFiber n (dwz63PlainMarginalWords K n t) c x).card + 1 := by
  have hid := card_dwz63PlainMarginalWords_eq K c n t hx
  unfold dwz63SharpDegree
  rw [hid, Nat.mul_div_cancel_left _ hpos]

/-! ## The reduction of `hcount` -/

/-- **`hcount` from a conditional upper bound and a fibre lower bound.**

`r` is defined so that the two estimates compose exactly; the only loss is `su · sl`. -/
theorem dwz63_hcount_of_rate
    {matchCard fibreCard degree : ℕ → ℕ}
    {rateCompat rateAlpha rateX rateZ hashK : ℝ} {su sl : ℕ → ℝ}
    (hsu : ∀ N, 0 ≤ su N) (hsl : ∀ N, 0 ≤ sl N)
    (hp : 0 ≤ rateCompat) (hX : 0 < rateX) (hZ : 0 < rateZ) (hK : 0 < hashK)
    (hdeg : ∀ N, fibreCard N ≤ degree N)
    (hupper : ∀ N, (matchCard N : ℝ) ≤ su N * (rateAlpha / rateZ) ^ N)
    (hlower : ∀ N, (hashK * rateAlpha / rateX) ^ N ≤ sl N * (fibreCard N : ℝ)) :
    ∀ N, (matchCard N : ℝ) * rateCompat ^ N ≤
      (su N * sl N) * (rateCompat * rateX / (rateZ * hashK)) ^ N * (degree N : ℝ) := by
  intro N
  have hbase : rateCompat * rateAlpha / rateZ =
      rateCompat * rateX / (rateZ * hashK) * (hashK * rateAlpha / rateX) := by
    field_simp
  have hsplit : (rateCompat * rateAlpha / rateZ) ^ N =
      (rateCompat * rateX / (rateZ * hashK)) ^ N * (hashK * rateAlpha / rateX) ^ N := by
    rw [hbase, mul_pow]
  have hrpow : (0 : ℝ) ≤ (rateCompat * rateX / (rateZ * hashK)) ^ N := by
    refine pow_nonneg ?_ N
    positivity
  have hdegR : (fibreCard N : ℝ) ≤ (degree N : ℝ) := by exact_mod_cast hdeg N
  calc (matchCard N : ℝ) * rateCompat ^ N
      ≤ (su N * (rateAlpha / rateZ) ^ N) * rateCompat ^ N :=
        mul_le_mul_of_nonneg_right (hupper N) (pow_nonneg hp N)
    _ = su N * (rateCompat * rateAlpha / rateZ) ^ N := by
        rw [mul_assoc, ← mul_pow]
        ring_nf
    _ = su N * ((rateCompat * rateX / (rateZ * hashK)) ^ N * (hashK * rateAlpha / rateX) ^ N) := by
        rw [hsplit]
    _ ≤ su N * ((rateCompat * rateX / (rateZ * hashK)) ^ N * (sl N * (fibreCard N : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (hsu N)
        exact mul_le_mul_of_nonneg_left (hlower N) hrpow
    _ = (su N * sl N) * (rateCompat * rateX / (rateZ * hashK)) ^ N * (fibreCard N : ℝ) := by ring
    _ ≤ (su N * sl N) * (rateCompat * rateX / (rateZ * hashK)) ^ N * (degree N : ℝ) := by
        refine mul_le_mul_of_nonneg_left hdegR ?_
        have := hsu N; have := hsl N
        positivity

end AlgebraicComplexity.Examples
