/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.BinomialEntropyEnvelope
import AlgebraicComplexity.Examples.CoppersmithWinogradEasyRectangularBound

/-!
# Huang--Pan's sharp rectangular bound (6.1) and `ω(1,1,2) < 3.3399`

`Examples/CoppersmithWinogradEasyRectangularBound.lean` reads Huang--Pan (6.2) and a *weak* form
of (6.1) off the whole-leg-fiber competitor bound.  This module runs the same schedule at the
type-restricted competitor count `easyRectTypedFiberBound` of
`Examples/CoppersmithWinogradEasyRectangularHashing.lean` and obtains (6.1) verbatim:

```text
ω(1, 1, r) ≤ log ((1+r)^(1+r) · (q+2)^(2+r) / (2+r)^(2+r)) / log q     (r ≥ 1, every field)
```

[HP98, Section 6.1, (6.1) on p. 273].

## What makes it sharp

For `b ≤ a` the type-restricted leg fiber is the binomial coefficient `binom(a+b, a)`
(`easyRectTypedFiberBound_eq_of_le`), and along the schedule `(a, b) = (pN, mN)` it is dominated
*exactly*, with no subexponential loss, by the `N`-th power of the two-letter entropy base

```text
Φ = Analysis.binomialEntropyBase p m = (p+m)^(p+m) / (p^p · m^m).
```

The envelope, its positivity, and its logarithm are the paper-independent method-of-types facts of
`Analysis/BinomialEntropyEnvelope.lean`; the exactness comes from
`Analysis.choose_mul_split_pow_le_one`: for `x + y = 1` and `x, y ≥ 0`, one term of the binomial
expansion of `(x+y)^n` is at most `1`.  Using the *loss-free* envelope rather than
`WordType.multinomial_le_upperLoss_mul_proportionalEntropyBase_pow` keeps the modulus of the
schedule geometric, which is what `Growth.sqrt_log_le_mul_sqrt_succ` needs; a linear-in-`N` loss
in the modulus would have to be absorbed into the base and would degrade the constant.

Dividing the trinomial entropy base `E₀` by `Φ` replaces the whole-fiber constant `2^(1+r) r^r`
by `(1+r)^(1+r)`, which is Huang--Pan's (6.1).  That division is exact in a stronger sense: the
trinomial base *factors* as `E₀ = binomialEntropyBase p m · binomialEntropyBase m (p+m)` along the
split `p + 2m = (p+m) + m`, so the sharp growth constant is again a two-letter entropy base and
both logarithm expansions are instances of `Analysis.log_binomialEntropyBase`.

## Main results

* `easyRectTypedFiberBound_scaled_le_sharp` -- the sharp competitor envelope
  `Analysis.binomialEntropyBase` along the Huang--Pan schedule;
* `easyRectEntropyBase_eq_binomialEntropyBase_mul`,
  `easyRectSharpGrowth_eq_binomialEntropyBase` -- the factorization of `E₀` and the resulting
  identity `E₀ / Φ = Analysis.binomialEntropyBase m (p+m)`;
* `easyRect_rectangularOmega_le_huangPan_sharp` -- (6.1) in denominator-free schedule form;
* `huangPan_rectangularOmega_le_of_one_le_sharp` -- **(6.1)** for every rational `r ≥ 1`;
* `huangPan_sharp_bound_one_eq_easyCW`, `huangPan_rectangularOmega_le_one_eq_easyCW_sharp` -- the
  faithfulness check at `r = 1`, where (6.1) is again `(4/27)·(q+2)^3`;
* `huangPan_rectangularOmega_two_le` -- the `r = 2` corollary
  `ω(1,1,2) ≤ log (27·(q+2)^4/256) / log q`;
* `huangPan_rectangularOmega_two_le_seven_log_three`, `huangPan_rectangularOmega_two_lt` -- at
  `q = 10` the constant is `27·12^4/256 = 2187 = 3^7` exactly, so `ω(1,1,2) ≤ 7 log 3 / log 10`,
  and the certified rational log enclosures of `Analysis/LogConstants.lean` give
  `ω(1,1,2) < 3.3399`.

## References

* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299; (6.1) on p. 273.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor Growth

universe u

/-- **The sharp competitor envelope along the Huang--Pan schedule**, for `m ≤ p` (that is
`r ≥ 1`), where the leg maximum is attained on the `y` and `z` legs. -/
theorem easyRectTypedFiberBound_scaled_le_sharp {p m : ℕ} (hp : 0 < p) (hm : 0 < m)
    (hmp : m ≤ p) (N : ℕ) :
    ((easyRectTypedFiberBound (p * N) (m * N) : ℕ) : ℝ) ≤
      Analysis.binomialEntropyBase p m ^ N := by
  have hcollapse : easyRectTypedFiberBound (p * N) (m * N) =
      Nat.choose (p * N + m * N) (p * N) :=
    easyRectTypedFiberBound_eq_of_le (Nat.mul_le_mul_right N hmp)
  rw [hcollapse, show p * N + m * N = (p + m) * N from by ring]
  exact Analysis.choose_scaled_le_binomialEntropyBase_pow hp hm N

/-! ## The trinomial base as a product of two binomial bases -/

/-- **The trinomial entropy base factors through the binomial one**, along the split
`p + 2m = (p + m) + m`:

`E₀ = binomialEntropyBase p m · binomialEntropyBase m (p+m)`.

Both logarithm expansions below are read off this identity, so neither has to redo the
`Real.log_div`/`Real.log_pow` bookkeeping of `Analysis.log_binomialEntropyBase`. -/
theorem easyRectEntropyBase_eq_binomialEntropyBase_mul {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    easyRectEntropyBase p m
      = Analysis.binomialEntropyBase p m * Analysis.binomialEntropyBase m (p + m) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsR : (0 : ℝ) < ((p + m : ℕ) : ℝ) := by
    have : 0 < p + m := by omega
    exact_mod_cast this
  have hm2 : (m : ℝ) ^ (2 * m) = (m : ℝ) ^ m * (m : ℝ) ^ m := by
    rw [two_mul, pow_add]
  have hsum : m + (p + m) = p + 2 * m := by omega
  unfold easyRectEntropyBase Analysis.binomialEntropyBase
  rw [hsum, hm2]
  field_simp

/-- **The sharp growth constant is itself a binomial entropy base.**  Dividing the trinomial base
`E₀` by the sharp envelope `Φ = binomialEntropyBase p m` cancels the `p^p` factor exactly and
leaves the two-letter base at `(m, p+m)`. -/
theorem easyRectSharpGrowth_eq_binomialEntropyBase {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    easyRectEntropyBase p m / Analysis.binomialEntropyBase p m
      = Analysis.binomialEntropyBase m (p + m) := by
  rw [easyRectEntropyBase_eq_binomialEntropyBase_mul hp hm, mul_comm, mul_div_assoc,
    div_self (Analysis.binomialEntropyBase_pos hp hm).ne', mul_one]

/-! ## Logarithms -/

/-- Explicit logarithm of the trinomial entropy base. -/
theorem log_easyRectEntropyBase {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    Real.log (easyRectEntropyBase p m) =
      ((p + 2 * m : ℕ) : ℝ) * Real.log ((p + 2 * m : ℕ) : ℝ)
        - (p : ℝ) * Real.log (p : ℝ) - 2 * (m : ℝ) * Real.log (m : ℝ) := by
  have hpm : 0 < p + m := by omega
  rw [easyRectEntropyBase_eq_binomialEntropyBase_mul hp hm,
    Real.log_mul (Analysis.binomialEntropyBase_pos hp hm).ne'
      (Analysis.binomialEntropyBase_pos hm hpm).ne',
    Analysis.log_binomialEntropyBase hp hm, Analysis.log_binomialEntropyBase hm hpm,
    show m + (p + m) = p + 2 * m from by omega]
  push_cast
  ring

/-- Logarithm of the sharp growth constant `E₀ / Φ`: the `p log p` terms cancel and one `m log m`
survives.  It is `Analysis.log_binomialEntropyBase` at `(m, p+m)`. -/
theorem log_easyRectSharpGrowth {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    Real.log (easyRectEntropyBase p m / Analysis.binomialEntropyBase p m) =
      ((p + 2 * m : ℕ) : ℝ) * Real.log ((p + 2 * m : ℕ) : ℝ)
        - (m : ℝ) * Real.log (m : ℝ)
        - ((p + m : ℕ) : ℝ) * Real.log ((p + m : ℕ) : ℝ) := by
  have hpm : 0 < p + m := by omega
  rw [easyRectSharpGrowth_eq_binomialEntropyBase hp hm,
    Analysis.log_binomialEntropyBase hm hpm, show m + (p + m) = p + 2 * m from by omega]

/-- Expansion of the logarithm of Huang--Pan's sharp bound. -/
theorem log_huangPanSharpForm {q : ℕ} {r : ℝ} (hr : 0 < r) :
    Real.log ((1 + r) ^ (1 + r) * ((q + 2 : ℕ) : ℝ) ^ (2 + r) / (2 + r) ^ (2 + r)) =
      (1 + r) * Real.log (1 + r) + (2 + r) * Real.log ((q + 2 : ℕ) : ℝ)
        - (2 + r) * Real.log (2 + r) := by
  have hq2 : (0 : ℝ) < ((q + 2 : ℕ) : ℝ) := by
    have : 0 < q + 2 := by omega
    exact_mod_cast this
  have h1r : (0 : ℝ) < 1 + r := by linarith
  have h2r : (0 : ℝ) < 2 + r := by linarith
  have hrr : (0 : ℝ) < (1 + r) ^ (1 + r) := Real.rpow_pos_of_pos h1r _
  have hq2p : (0 : ℝ) < ((q + 2 : ℕ) : ℝ) ^ (2 + r) := Real.rpow_pos_of_pos hq2 _
  have h2rp : (0 : ℝ) < (2 + r) ^ (2 + r) := Real.rpow_pos_of_pos h2r _
  rw [Real.log_div (mul_pos hrr hq2p).ne' h2rp.ne',
    Real.log_mul hrr.ne' hq2p.ne',
    Real.log_rpow h1r, Real.log_rpow hq2, Real.log_rpow h2r]

/-! ## The sharp bound in denominator-free form -/

section Bound

variable (K : Type u) [Field K]

/-- Logarithmic form of the sharp master inequality. -/
theorem easyRect_rectangularOmega_le_log_sharp (q p m : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) (hmp : m ≤ p) :
    rectangularOmega K (easyRectKappa p m) ≤
      (((p + 2 * m : ℕ) : ℝ) * Real.log ((q + 2 : ℕ) : ℝ)
          - Real.log (easyRectEntropyBase p m / Analysis.binomialEntropyBase p m))
        / ((m : ℝ) * Real.log q) := by
  have hmaster := easyRect_master_inequality_of_fiberGrowth K q p m hq hp hm
    (Analysis.one_le_binomialEntropyBase hp hm) (easyRectTypedFiberBound_scaled_le_sharp hp hm hmp)
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hGpos : 0 < easyRectEntropyBase p m / Analysis.binomialEntropyBase p m :=
    div_pos (easyRectEntropyBase_pos hp hm) (Analysis.binomialEntropyBase_pos hp hm)
  set ω : ℝ := rectangularOmega K (easyRectKappa p m) with hωdef
  have hYpos : (0 : ℝ) < (q : ℝ) ^ ((m : ℝ) * ω) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hlog := Real.log_le_log (mul_pos hGpos hYpos) hmaster
  rw [Real.log_mul hGpos.ne' hYpos.ne', Real.log_rpow (by linarith), Real.log_pow] at hlog
  rw [le_div_iff₀ (by positivity),
    show ω * ((m : ℝ) * Real.log (q : ℝ)) = ((m : ℝ) * ω) * Real.log (q : ℝ) from by ring]
  linarith

/-- **Huang--Pan (6.1), denominator-free form.**

`ω(1, 1, p/m) ≤ log ((1+r)^(1+r) · (q+2)^(2+r) / (2+r)^(2+r)) / log q` with `r = p/m ≥ 1`. -/
theorem easyRect_rectangularOmega_le_huangPan_sharp (q p m : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) (hmp : m ≤ p) :
    rectangularOmega K (easyRectKappa p m) ≤
      Real.log ((1 + easyRectKappa p m) ^ (1 + easyRectKappa p m)
          * ((q + 2 : ℕ) : ℝ) ^ (2 + easyRectKappa p m)
          / (2 + easyRectKappa p m) ^ (2 + easyRectKappa p m)) / Real.log q := by
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hlqne : Real.log (q : ℝ) ≠ 0 := hlogq.ne'
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := hmR.ne'
  have hsR : (0 : ℝ) < ((p + 2 * m : ℕ) : ℝ) := by
    have : 0 < p + 2 * m := by omega
    exact_mod_cast this
  have htR : (0 : ℝ) < ((p + m : ℕ) : ℝ) := by
    have : 0 < p + m := by omega
    exact_mod_cast this
  have hrval : easyRectKappa p m = (p : ℝ) / (m : ℝ) := rfl
  have hrpos : 0 < easyRectKappa p m := by rw [hrval]; positivity
  refine (easyRect_rectangularOmega_le_log_sharp K q p m hq hp hm hmp).trans_eq ?_
  have h1r : (1 : ℝ) + easyRectKappa p m = ((p + m : ℕ) : ℝ) / (m : ℝ) := by
    rw [hrval]
    push_cast
    field_simp
    ring
  have h2r : (2 : ℝ) + easyRectKappa p m = ((p + 2 * m : ℕ) : ℝ) / (m : ℝ) := by
    rw [hrval]
    push_cast
    field_simp
    ring
  have hlog1r : Real.log (1 + easyRectKappa p m)
      = Real.log ((p + m : ℕ) : ℝ) - Real.log (m : ℝ) := by
    rw [h1r, Real.log_div htR.ne' hmR.ne']
  have hlog2r : Real.log (2 + easyRectKappa p m)
      = Real.log ((p + 2 * m : ℕ) : ℝ) - Real.log (m : ℝ) := by
    rw [h2r, Real.log_div hsR.ne' hmR.ne']
  rw [log_huangPanSharpForm (q := q) hrpos, log_easyRectSharpGrowth hp hm,
    hlog1r, hlog2r, h1r, h2r]
  push_cast
  field_simp
  ring

end Bound

/-! ## The `r ≥ 1` branch -/

section Branch

variable (K : Type u) [Field K]

/-- **Huang--Pan (6.1).**  For every rational `r ≥ 1` the easy Coppersmith--Winograd construction
gives, over every field,

`ω(1, 1, r) ≤ log ((1+r)^(1+r) · (q+2)^(2+r) / (2+r)^(2+r)) / log q`.

This is the sharp form: the competitor list is the type-restricted leg fiber
`binom((1+r)N; N, rN)` of `card_easyRectTypedWordMapFiber`, exactly as on p. 273, rather than the
whole fiber `2^{(1+r)N}` of `huangPan_rectangularOmega_le_of_one_le`. -/
theorem huangPan_rectangularOmega_le_of_one_le_sharp (q : ℕ) (hq : 1 < q) {r : ℚ} (hr : 1 ≤ r) :
    rectangularOmega K ((r : ℝ)) ≤
      Real.log ((1 + (r : ℝ)) ^ (1 + (r : ℝ)) * ((q + 2 : ℕ) : ℝ) ^ (2 + (r : ℝ))
        / (2 + (r : ℝ)) ^ (2 + (r : ℝ))) / Real.log q := by
  have hpos : (0 : ℚ) < r := lt_of_lt_of_le zero_lt_one hr
  set p : ℕ := r.num.natAbs with hpdef
  set m : ℕ := r.den with hmdef
  have hmpos : 0 < m := r.pos
  have hnum : (0 : ℤ) < r.num := Rat.num_pos.mpr hpos
  have hppos : 0 < p := Int.natAbs_pos.mpr hnum.ne'
  have hkappa : easyRectKappa p m = (r : ℝ) := easyRectKappa_num_den hpos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hmle : m ≤ p := by
    have h1 : (1 : ℝ) ≤ ((r : ℝ)) := by exact_mod_cast hr
    rw [← hkappa] at h1
    rw [show easyRectKappa p m = (p : ℝ) / (m : ℝ) from rfl, le_div_iff₀ hmR] at h1
    have h2 : (m : ℝ) ≤ (p : ℝ) := by linarith
    exact_mod_cast h2
  have hbound := easyRect_rectangularOmega_le_huangPan_sharp K q p m hq hppos hmpos hmle
  rwa [hkappa] at hbound

end Branch

/-! ## Faithfulness at `r = 1` -/

/-- At `r = 1` the sharp Huang--Pan expression is again the equal-type constant `(4/27)·(q+2)^3`
of `easyCW_omega_le_log`: `(1+1)^(1+1) = 4` and `(2+1)^(2+1) = 27`. -/
theorem huangPan_sharp_bound_one_eq_easyCW (q : ℕ) :
    (1 + (((1 : ℚ) : ℝ))) ^ (1 + (((1 : ℚ) : ℝ)))
        * ((q + 2 : ℕ) : ℝ) ^ (2 + (((1 : ℚ) : ℝ)))
        / (2 + (((1 : ℚ) : ℝ))) ^ (2 + (((1 : ℚ) : ℝ)))
      = (4 / 27 : ℝ) * (((q + 2 : ℕ) : ℝ) ^ 3) := by
  have h1 : (((1 : ℚ) : ℝ)) = (1 : ℝ) := by norm_num
  have e2 : (1 : ℝ) + (1 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  have e3 : (2 : ℝ) + (1 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  rw [h1, e2, e3, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]
  norm_num
  ring

/-- **Faithfulness check.**  At `r = 1` the sharp rectangular theorem is, as a statement, exactly
the equal-type theorem `easyCW_omega_le_log` of `Examples/CoppersmithWinogradEasyHashing.lean`. -/
theorem huangPan_rectangularOmega_le_one_eq_easyCW_sharp (K : Type u) [Field K] (q : ℕ) :
    (rectangularOmega K (((1 : ℚ) : ℝ)) ≤
        Real.log ((1 + (((1 : ℚ) : ℝ))) ^ (1 + (((1 : ℚ) : ℝ)))
          * ((q + 2 : ℕ) : ℝ) ^ (2 + (((1 : ℚ) : ℝ)))
          / (2 + (((1 : ℚ) : ℝ))) ^ (2 + (((1 : ℚ) : ℝ)))) / Real.log q) ↔
      (omega K ≤ Real.log ((4 / 27 : ℝ) * (((q + 2 : ℕ) : ℝ) ^ 3)) / Real.log q) := by
  rw [huangPan_sharp_bound_one_eq_easyCW q, show (((1 : ℚ) : ℝ)) = (1 : ℝ) from by norm_num,
    rectangularOmega_one]

/-! ## The headline numerical corollary at `r = 2` -/

section Numeric

variable (K : Type u) [Field K]

/-- At `r = 2` the sharp Huang--Pan expression is `27·(q+2)^4/256`. -/
theorem huangPan_sharp_bound_two_eq (q : ℕ) :
    (1 + (((2 : ℚ) : ℝ))) ^ (1 + (((2 : ℚ) : ℝ)))
        * ((q + 2 : ℕ) : ℝ) ^ (2 + (((2 : ℚ) : ℝ)))
        / (2 + (((2 : ℚ) : ℝ))) ^ (2 + (((2 : ℚ) : ℝ)))
      = 27 * ((q + 2 : ℕ) : ℝ) ^ (4 : ℕ) / 256 := by
  have h2 : (((2 : ℚ) : ℝ)) = (2 : ℝ) := by norm_num
  have e3 : (1 : ℝ) + (2 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  have e4 : (2 : ℝ) + (2 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  rw [h2, e3, e4, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]
  norm_num

/-- **The `r = 2` case of Huang--Pan (6.1):** `ω(1,1,2) ≤ log (27·(q+2)^4/256) / log q` over every
field and for every `q > 1`. -/
theorem huangPan_rectangularOmega_two_le (q : ℕ) (hq : 1 < q) :
    rectangularOmega K 2 ≤
      Real.log (27 * ((q + 2 : ℕ) : ℝ) ^ (4 : ℕ) / 256) / Real.log q := by
  have h := huangPan_rectangularOmega_le_of_one_le_sharp K q hq (r := 2) (by norm_num)
  rw [huangPan_sharp_bound_two_eq q] at h
  simpa using h

/-- **`ω(1,1,2) ≤ 7 log 3 / log 10`.**  At `q = 10` the Huang--Pan constant is
`27 · 12^4 / 256 = 2187 = 3^7` exactly, so the bound is a ratio of two logarithms of integers. -/
theorem huangPan_rectangularOmega_two_le_seven_log_three :
    rectangularOmega K 2 ≤ 7 * Real.log 3 / Real.log 10 := by
  have h := huangPan_rectangularOmega_two_le K 10 (by norm_num)
  have hval : (27 : ℝ) * ((10 + 2 : ℕ) : ℝ) ^ (4 : ℕ) / 256 = (3 : ℝ) ^ (7 : ℕ) := by
    norm_num
  rw [hval, Real.log_pow] at h
  have hc : (((10 : ℕ)) : ℝ) = (10 : ℝ) := by norm_num
  rw [hc] at h
  exact_mod_cast h

/-- **`ω(1,1,2) < 3.3399`.**  The exact-rational certificate: `7 log 3 ≤ 7.6902860216` and
`3.3399 · log 10 = 3.3399 · (log 2 + log 5) ≥ 7.6904039514`, using the ten-digit enclosures
`log_three_le_sharp`, `log_two_ge_sharp` and `log_five_ge_sharp` of `Analysis/LogConstants.lean`.
No floating-point evaluation and no `native_decide` enters the argument. -/
theorem huangPan_rectangularOmega_two_lt : rectangularOmega K 2 < 3.3399 := by
  refine (huangPan_rectangularOmega_two_le_seven_log_three K).trans_lt ?_
  have hlog10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 from by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hpos : 0 < Real.log 10 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ hpos, hlog10, show (3.3399 : ℝ) = 33399 / 10000 from by norm_num]
  linarith [Analysis.log_three_le_sharp, Analysis.log_two_ge_sharp, Analysis.log_five_ge_sharp]

end Numeric

end AlgebraicComplexity.Examples
