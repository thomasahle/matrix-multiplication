/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainCount
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalStage
import AlgebraicComplexity.Analysis.ConditionalLegFiberGrowth

set_option autoImplicit false

/-!
# The two pushed entropy bases of the plain fifteen-block profile, and `hupper`

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoCountComparison.lean`'s
`dwz63_hcount_of_rate` takes two conditional type-class estimates.  This module supplies the first
of them and the arithmetic both of them share.

## The shared arithmetic: `pushedTypeFiberEntropyBase` at the plain profile

`Combinatorics/PushedProfileFiberGrowth.lean`'s `pushedTypeFiberEntropyBase f profile` is
`proportionalEntropyBase profile / proportionalEntropyBase (mappedType f profile)`, and its `t`-th
power is the *per-block* form of the per-position ratio `ᾱ_α / ᾱ_c`.  At the plain partition
the
pushforward along `dwz63PlainLegRead c` is the committed `dwz63AlphaMarginal c`
(`mappedType_dwz63PlainLegRead`), so `dwz63_pushedTypeFiberEntropyBase_pow` evaluates the base at
the forced word length `n + 1 = 10 ^ 8 · t` as

`(ᾱ_α / exp H(α_c)) ^ (n + 1)`,   `ᾱ_α = exp H(α)` = `dwz63PlainRateAlpha`,

and its two leg instances read off `Examples/DuanWuZhouLevelTwoGlobalArithmetic.lean`'s atoms
`dwz63EntropyX` and `dwz63EntropyZ` through the committed `profileEntropyNats_dwz63AlphaX` and
`profileEntropyNats_dwz63AlphaZ`.

`ᾱ_α` itself is never evaluated, and does not need to be: it appears in `hupper` and in `hlower`
with opposite signs and **cancels** in `dwz63_hcount_of_rate`'s conclusion, whose rate is
`r = ᾱ_p ᾱ_X / (ᾱ_Z K)`.  So no `H(α)` enclosure enters the count comparison.

## `hupper`: the conditional upper bound on `|matchable α K|`

`CompatibleSplit.SplitRequirements.matchable αType K` is by definition
`WordType.typedWordMapFiber S.zIndex αType K` — the large triples of the prescribed joint type
through a fixed large `Z`-block.  At the plain partition `S.zIndex` is `dwz63PlainLegRead .Z` and
`αType` is `proportionalCounts dwz63PlainAlpha t`, so the estimate needed is exactly an upper
bound on one typed word-map fibre, and every ingredient is committed:

* `WordType.card_pushedTypeClass_mul_card_typedFiber` — the exact double count
  `N_Z · fibre = N_α`;
* `WordType.proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass` — the zero-safe
  *lower* bound `ᾱ_Z ^ t ≤ loss · N_Z` on the denominator;
* `WordType.card_proportionalTypeClass_le_entropyBase_pow` — the **loss-free** upper bound
  `N_α ≤ ᾱ_α ^ t` on the numerator;
* `WordType.fiberCard_le_mul_div_pow_of_conditional_mul_fiber_le` — the division-free arithmetic
  core that combines the three.

The only slack is the structural-zero Stirling loss of the `Z` marginal, which
`WordType.structuralZeroMultinomialLoss_subexponential` makes subexponential.  In particular the
hash-loss multiplier `K = 1 + 10⁻¹⁰` does **not** appear here: `matchable` is a *joint*
type-class
condition, so the Gibbs deficit — which bounds the marginal-typical ambient above by `K ^ n` times
the joint typical count — is not needed for this direction.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`), §6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

open scoped BigOperators

/-! ## `ᾱ_α`, the per-position rate of the plain joint typical count -/

/-- **`ᾱ_α` at the plain fifteen-block partition**: the exponential of the natural-logarithm
entropy of `dwz63PlainAlpha`.  It is never evaluated numerically — it cancels between `hupper` and
`hlower`. -/
noncomputable def dwz63PlainRateAlpha : ℝ :=
  Real.exp (WordType.profileEntropyNats dwz63PlainAlpha)

theorem dwz63PlainRateAlpha_pos : 0 < dwz63PlainRateAlpha :=
  Real.exp_pos _

/-- The natural-number scalar form of the exponential power law, stated here so that both the `X`
and the `Z` evaluation below use one and the same spelling. -/
theorem dwz63_exp_natCast_mul (m : ℕ) (x : ℝ) :
    Real.exp ((m : ℝ) * x) = Real.exp x ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hstep : ((k + 1 : ℕ) : ℝ) * x = (k : ℝ) * x + x := by push_cast; ring
      rw [hstep, Real.exp_add, ih, pow_succ]

theorem dwz63_plainAlpha_profileMass_pos :
    0 < WordType.profileMass dwz63PlainAlpha := by
  rw [profileMass_dwz63PlainAlpha]
  norm_num

/-! ## The pushed entropy base at the plain partition -/

/-- **The pushed fibre base of the plain profile on leg `c`, at the forced word length.**

`pushedTypeFiberEntropyBase` is a per-block quantity; raised to the block count `t` it is the
per-position ratio `ᾱ_α / exp H(α_c)` raised to the word length `N = 10 ^ 8 · t`. -/
theorem dwz63_pushedTypeFiberEntropyBase_pow (c : Leg) {t N : ℕ}
    (hlen : WordType.profileMass dwz63PlainAlpha * t = N) :
    WordType.pushedTypeFiberEntropyBase (dwz63PlainLegRead c) dwz63PlainAlpha ^ t =
      (dwz63PlainRateAlpha /
        Real.exp (WordType.profileEntropyNats (dwz63AlphaMarginal c))) ^ N := by
  have hkey : Real.exp ((WordType.profileMass dwz63PlainAlpha : ℝ) *
        (WordType.profileEntropyNats dwz63PlainAlpha -
          WordType.profileEntropyNats (dwz63AlphaMarginal c))) ^ t =
      (dwz63PlainRateAlpha /
        Real.exp (WordType.profileEntropyNats (dwz63AlphaMarginal c))) ^ N := by
    calc Real.exp ((WordType.profileMass dwz63PlainAlpha : ℝ) *
            (WordType.profileEntropyNats dwz63PlainAlpha -
              WordType.profileEntropyNats (dwz63AlphaMarginal c))) ^ t
        = Real.exp ((t : ℝ) * ((WordType.profileMass dwz63PlainAlpha : ℝ) *
            (WordType.profileEntropyNats dwz63PlainAlpha -
              WordType.profileEntropyNats (dwz63AlphaMarginal c)))) :=
          (dwz63_exp_natCast_mul t _).symm
      _ = Real.exp ((N : ℝ) *
            (WordType.profileEntropyNats dwz63PlainAlpha -
              WordType.profileEntropyNats (dwz63AlphaMarginal c))) := by
          congr 1
          rw [← hlen]
          push_cast
          ring
      _ = Real.exp (WordType.profileEntropyNats dwz63PlainAlpha -
            WordType.profileEntropyNats (dwz63AlphaMarginal c)) ^ N :=
          dwz63_exp_natCast_mul N _
      _ = (dwz63PlainRateAlpha /
            Real.exp (WordType.profileEntropyNats (dwz63AlphaMarginal c))) ^ N := by
          rw [Real.exp_sub, dwz63PlainRateAlpha]
  rw [WordType.pushedTypeFiberEntropyBase_eq_exp_entropyDifference _ _
    dwz63_plainAlpha_profileMass_pos, mappedType_dwz63PlainLegRead c]
  exact hkey

/-- **The `X`-leg pushed base**, read against `GlobalArithmetic`'s `dwz63EntropyX`. -/
theorem dwz63_pushedTypeFiberEntropyBase_X_pow {t N : ℕ}
    (hlen : WordType.profileMass dwz63PlainAlpha * t = N) :
    WordType.pushedTypeFiberEntropyBase (dwz63PlainLegRead .X) dwz63PlainAlpha ^ t =
      (dwz63PlainRateAlpha / Real.exp dwz63EntropyX) ^ N := by
  rw [dwz63_pushedTypeFiberEntropyBase_pow .X hlen, dwz63AlphaMarginal_X,
    profileEntropyNats_dwz63AlphaX]

/-- **The `Z`-leg pushed base**, read against `GlobalArithmetic`'s `dwz63EntropyZ`. -/
theorem dwz63_pushedTypeFiberEntropyBase_Z_pow {t N : ℕ}
    (hlen : WordType.profileMass dwz63PlainAlpha * t = N) :
    WordType.pushedTypeFiberEntropyBase (dwz63PlainLegRead .Z) dwz63PlainAlpha ^ t =
      (dwz63PlainRateAlpha / Real.exp dwz63EntropyZ) ^ N := by
  rw [dwz63_pushedTypeFiberEntropyBase_pow .Z hlen, dwz63AlphaMarginal_Z,
    profileEntropyNats_dwz63AlphaZ]

/-! ## `hupper`, at one fixed word length -/

/-- The plain `Z`-leg pushforward of the joint profile is the committed `Z` marginal. -/
theorem dwz63_mappedType_plainLegRead_Z :
    WordType.mappedType (dwz63PlainLegRead .Z) dwz63PlainAlpha = dwz63AlphaZ := by
  rw [mappedType_dwz63PlainLegRead, dwz63AlphaMarginal_Z]

-- ELABORATION RISK: the final `rw` chain rewrites the pushed profile
-- `mappedType (dwz63PlainLegRead .Z) dwz63PlainAlpha` to `dwz63AlphaZ` under both a
-- `structuralZeroMultinomialLoss` and a `proportionalEntropyBase`.  Fallback if `congr 1` splits
-- the product the wrong way: replace `congr 1` by
-- `refine congrArg₂ (· * ·) rfl ?_`.
/-- **`hupper` at one word length.**

`|matchable α K| ≤ loss(α_Z) · (ᾱ_α / ᾱ_Z) ^ N`, with the *loss-free* method-of-types
upper bound
on the numerator and the zero-safe Stirling lower bound on the denominator.  The left side is
`CompatibleSplit.SplitRequirements.matchable` unfolded: that definition **is**
`WordType.typedWordMapFiber S.zIndex αType K`. -/
theorem dwz63_card_typedWordMapFiber_Z_le {t N : ℕ} (ht : 0 < t)
    (hlen : WordType.profileMass dwz63PlainAlpha * t = N)
    (Kword : Fin N → Fin 5)
    (hK : WordType.multiplicity Kword = WordType.proportionalCounts dwz63AlphaZ t) :
    ((WordType.typedWordMapFiber (dwz63PlainLegRead .Z)
        (WordType.proportionalCounts dwz63PlainAlpha t) Kword).card : ℝ) ≤
      WordType.structuralZeroMultinomialLoss dwz63AlphaZ t *
        (dwz63PlainRateAlpha / Real.exp dwz63EntropyZ) ^ N := by
  subst hlen
  have htarget : Kword ∈ WordType.typeClass
      (WordType.profileMass dwz63PlainAlpha * t)
      (WordType.proportionalCounts
        (WordType.mappedType (dwz63PlainLegRead .Z) dwz63PlainAlpha) t) := by
    rw [WordType.mem_typeClass, dwz63_mappedType_plainLegRead_Z]
    exact hK
  have hfactor := WordType.card_pushedTypeClass_mul_card_typedFiber
    (dwz63PlainLegRead .Z) dwz63PlainAlpha t Kword htarget
  have hcond := WordType.proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass
    (WordType.mappedType (dwz63PlainLegRead .Z) dwz63PlainAlpha) t
  rw [WordType.profileMass_mappedType] at hcond
  have hambient := WordType.card_proportionalTypeClass_le_entropyBase_pow
    dwz63PlainAlpha dwz63_plainAlpha_profileMass_pos t ht
  have hres := WordType.fiberCard_le_mul_div_pow_of_conditional_mul_fiber_le
    (WordType.proportionalEntropyBase
      (WordType.mappedType (dwz63PlainLegRead .Z) dwz63PlainAlpha))
    (WordType.proportionalEntropyBase dwz63PlainAlpha)
    (WordType.structuralZeroMultinomialLoss
      (WordType.mappedType (dwz63PlainLegRead .Z) dwz63PlainAlpha) t)
    1 t
    (WordType.typeClass (WordType.profileMass dwz63PlainAlpha * t)
      (WordType.proportionalCounts
        (WordType.mappedType (dwz63PlainLegRead .Z) dwz63PlainAlpha) t)).card
    (WordType.typedWordMapFiber (dwz63PlainLegRead .Z)
      (WordType.proportionalCounts dwz63PlainAlpha t) Kword).card
    (WordType.typeClass (WordType.profileMass dwz63PlainAlpha * t)
      (WordType.proportionalCounts dwz63PlainAlpha t)).card
    (WordType.proportionalEntropyBase_pos_zeroSafe _)
    (WordType.structuralZeroMultinomialLoss_pos _ t).le
    hcond (le_of_eq hfactor) (by rw [one_mul]; exact hambient)
  rw [mul_one] at hres
  refine hres.trans_eq ?_
  rw [dwz63_mappedType_plainLegRead_Z]
  congr 1
  rw [← dwz63_pushedTypeFiberEntropyBase_Z_pow (t := t) rfl]
  simp only [WordType.pushedTypeFiberEntropyBase, dwz63_mappedType_plainLegRead_Z]

end AlgebraicComplexity.Examples
