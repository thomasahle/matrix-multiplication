/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradEasyRectangularRate

/-!
# Huang--Pan's rectangular Coppersmith--Winograd bounds

This module reads Huang--Pan's Section 6 bounds off the master inequality
`easyRect_master_inequality` of `Examples/CoppersmithWinogradEasyRectangularRate.lean`.

## Main results

* `huangPan_rectangularOmega_le_of_le_one` -- Huang--Pan **(6.2)**, for `0 ≤ r ≤ 1`:
  `ω(1,1,r) ≤ log (4 · r^r · (q+2)^(2+r) / (2+r)^(2+r)) / log q`;
* `huangPan_rectangularOmega_le_of_one_le` -- the `r ≥ 1` branch, in the form the *whole-fiber*
  competitor bound of `card_easyRectLegWordMapFiber` supplies:
  `ω(1,1,r) ≤ log (2^(1+r) · r^r · (q+2)^(2+r) / (2+r)^(2+r)) / log q`;
* `huangPan_bound_one_eq_easyCW` and `huangPan_rectangularOmega_le_one_eq_easyCW` -- the
  faithfulness check at `r = 1`: both branches reduce, *as stated*, to
  `easyCW_omega_le_log : omega K ≤ log ((4/27)·(q+2)^3) / log q`.

## The two forms of the `r > 1` branch

For `r ≥ 1` Huang--Pan's (6.1) uses the sharper competitor list
`M = 2·((1+r)N; N, rN) + 1`, the type-*restricted* leg fiber, in place of the whole fiber
`2^{(1+r)N}` that this module bounds by.  The two agree exactly at `r = 1` — which is why
the `r ≤ 1` branch is Huang--Pan's (6.2) verbatim — and diverge for `r ≠ 1`.  The restricted count
is `card_easyRectTypedWordMapFiber`; running the same schedule at it gives the sharp (6.1) and the
numerical corollary `ω(1,1,2) < 3.3399` in
`Examples/CoppersmithWinogradEasyRectangularSharpBound.lean`.  The weak branch below is kept
because it needs no binomial entropy estimate at all, and because it is the `r ≥ 1` instance of the
single whole-fiber statement `easyRect_rectangularOmega_le_huangPan` that also carries (6.2).

## References

* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299; (6.1) on p. 273, (6.2) on p. 274.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor Growth

universe u

/-! ## Logarithms of the two sides -/

/-- Explicit logarithm of the growth constant of the rectangular schedule. -/
theorem log_easyRectGrowth {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    Real.log (easyRectGrowth p m) =
      ((p + 2 * m : ℕ) : ℝ) * Real.log ((p + 2 * m : ℕ) : ℝ)
        - (p : ℝ) * Real.log (p : ℝ) - 2 * (m : ℝ) * Real.log (m : ℝ)
        - ((easyRectFiberExponent p m : ℕ) : ℝ) * Real.log 2 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsR : (0 : ℝ) < ((p + 2 * m : ℕ) : ℝ) := by
    have : 0 < p + 2 * m := by omega
    exact_mod_cast this
  have hden : ((2 ^ easyRectFiberExponent p m : ℕ) : ℝ) =
      (2 : ℝ) ^ easyRectFiberExponent p m := by push_cast; ring
  have hA : (0 : ℝ) < ((p + 2 * m : ℕ) : ℝ) ^ (p + 2 * m) := pow_pos hsR _
  have hP : (0 : ℝ) < (p : ℝ) ^ p := pow_pos hpR _
  have hM : (0 : ℝ) < (m : ℝ) ^ (2 * m) := pow_pos hmR _
  have hT : (0 : ℝ) < (2 : ℝ) ^ easyRectFiberExponent p m := pow_pos (by norm_num) _
  unfold easyRectGrowth easyRectEntropyBase
  rw [hden, Real.log_div (div_pos hA (mul_pos hP hM)).ne' hT.ne',
    Real.log_div hA.ne' (mul_pos hP hM).ne',
    Real.log_mul hP.ne' hM.ne',
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- Expansion of the logarithm of Huang--Pan's bound. -/
theorem log_huangPanForm {q : ℕ} {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    Real.log (c * r ^ r * ((q + 2 : ℕ) : ℝ) ^ (2 + r) / (2 + r) ^ (2 + r)) =
      Real.log c + r * Real.log r + (2 + r) * Real.log ((q + 2 : ℕ) : ℝ)
        - (2 + r) * Real.log (2 + r) := by
  have hq2 : (0 : ℝ) < ((q + 2 : ℕ) : ℝ) := by
    have : 0 < q + 2 := by omega
    exact_mod_cast this
  have h2r : (0 : ℝ) < 2 + r := by linarith
  have hrr : (0 : ℝ) < r ^ r := Real.rpow_pos_of_pos hr r
  have hq2p : (0 : ℝ) < ((q + 2 : ℕ) : ℝ) ^ (2 + r) := Real.rpow_pos_of_pos hq2 _
  have h2rp : (0 : ℝ) < (2 + r) ^ (2 + r) := Real.rpow_pos_of_pos h2r _
  rw [Real.log_div (mul_pos (mul_pos hc hrr) hq2p).ne' h2rp.ne',
    Real.log_mul (mul_pos hc hrr).ne' hq2p.ne',
    Real.log_mul hc.ne' hrr.ne',
    Real.log_rpow hr, Real.log_rpow hq2, Real.log_rpow h2r]

/-! ## The bound in denominator-free form -/

section Bound

variable (K : Type u) [Field K]

/-- Logarithmic form of the master inequality: `ω(1,1,p/m)` is bounded by the Huang--Pan
expression written in terms of the integer schedule parameters. -/
theorem easyRect_rectangularOmega_le_log (q p m : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) :
    rectangularOmega K (easyRectKappa p m) ≤
      (((p + 2 * m : ℕ) : ℝ) * Real.log ((q + 2 : ℕ) : ℝ)
          - Real.log (easyRectGrowth p m)) / ((m : ℝ) * Real.log q) := by
  have hmaster := easyRect_master_inequality K q p m hq hp hm
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hGpos : 0 < easyRectGrowth p m := easyRectGrowth_pos hp hm
  set ω : ℝ := rectangularOmega K (easyRectKappa p m) with hωdef
  have hYpos : (0 : ℝ) < (q : ℝ) ^ ((m : ℝ) * ω) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hlog := Real.log_le_log (mul_pos hGpos hYpos) hmaster
  rw [Real.log_mul hGpos.ne' hYpos.ne', Real.log_rpow (by linarith), Real.log_pow] at hlog
  rw [le_div_iff₀ (by positivity),
    show ω * ((m : ℝ) * Real.log (q : ℝ)) = ((m : ℝ) * ω) * Real.log (q : ℝ) from by ring]
  linarith

/-- **Huang--Pan's Section 6 bound, denominator-free form.**

`ω(1, 1, p/m) ≤ log (2^(Λ/m) · r^r · (q+2)^(2+r) / (2+r)^(2+r)) / log q` with `r = p/m` and
`Λ = max (2m, p+m)`.  The two branches of Section 6 are the two possible values of `Λ/m`: it is
`2` when `p ≤ m` and `1 + r` when `m ≤ p`. -/
theorem easyRect_rectangularOmega_le_huangPan (q p m : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) :
    rectangularOmega K (easyRectKappa p m) ≤
      Real.log ((2 : ℝ) ^ (((easyRectFiberExponent p m : ℕ) : ℝ) / (m : ℝ))
          * easyRectKappa p m ^ (easyRectKappa p m)
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
  have hrval : easyRectKappa p m = (p : ℝ) / (m : ℝ) := rfl
  have hrpos : 0 < easyRectKappa p m := by rw [hrval]; positivity
  have hcpos : (0 : ℝ) < (2 : ℝ) ^ (((easyRectFiberExponent p m : ℕ) : ℝ) / (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  refine (easyRect_rectangularOmega_le_log K q p m hq hp hm).trans_eq ?_
  have hlogr : Real.log (easyRectKappa p m) = Real.log (p : ℝ) - Real.log (m : ℝ) := by
    rw [hrval, Real.log_div hpR.ne' hmR.ne']
  have h2r : (2 : ℝ) + easyRectKappa p m = ((p + 2 * m : ℕ) : ℝ) / (m : ℝ) := by
    rw [hrval]
    push_cast
    field_simp
    ring
  have hlog2r : Real.log (2 + easyRectKappa p m)
      = Real.log ((p + 2 * m : ℕ) : ℝ) - Real.log (m : ℝ) := by
    rw [h2r, Real.log_div hsR.ne' hmR.ne']
  rw [log_huangPanForm (q := q) hcpos hrpos, Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    log_easyRectGrowth hp hm, hlogr, hlog2r, h2r, hrval]
  push_cast
  field_simp
  ring

end Bound

/-! ## The two branches of Huang--Pan Section 6 -/

section Branches

variable (K : Type u) [Field K]

/-- A positive rational is `easyRectKappa` of its numerator and denominator.  A tower-local
spelling of `AlgebraicComplexity.rectAspectRatio_num_den`. -/
theorem easyRectKappa_num_den {r : ℚ} (hr : 0 < r) :
    easyRectKappa r.num.natAbs r.den = (r : ℝ) :=
  rectAspectRatio_num_den hr

/-- **Huang--Pan (6.2).**  For `0 ≤ r ≤ 1` the easy Coppersmith--Winograd construction gives

`ω(1, 1, r) ≤ log (4 · r^r · (q+2)^(2+r) / (2+r)^(2+r)) / log q`

over every field.  This is the regime in which the whole-leg-fiber competitor bound
`card_easyRectLegWordMapFiber` is first-order sharp, so the constant is Huang--Pan's. -/
theorem huangPan_rectangularOmega_le_of_le_one (q : ℕ) (hq : 1 < q) {r : ℚ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    rectangularOmega K ((r : ℝ)) ≤
      Real.log (4 * (r : ℝ) ^ ((r : ℝ)) * ((q + 2 : ℕ) : ℝ) ^ (2 + (r : ℝ))
        / (2 + (r : ℝ)) ^ (2 + (r : ℝ))) / Real.log q := by
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  rcases eq_or_lt_of_le hr₀ with hzero | hpos
  · -- The degenerate ratio `r = 0`, where `ω(1,1,0) = 2` outright.
    have hrR : ((r : ℝ)) = 0 := by rw [← hzero]; norm_num
    rw [hrR, rectangularOmega_zero]
    have e1 : (2 : ℝ) + (0 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    have hval : (4 : ℝ) * (0 : ℝ) ^ (0 : ℝ) * ((q + 2 : ℕ) : ℝ) ^ (2 + (0 : ℝ))
        / (2 + (0 : ℝ)) ^ (2 + (0 : ℝ)) = ((q + 2 : ℕ) : ℝ) ^ (2 : ℕ) := by
      rw [Real.rpow_zero, e1, Real.rpow_natCast, Real.rpow_natCast]
      norm_num
    rw [hval, Real.log_pow, le_div_iff₀ hlogq]
    have hmono : Real.log (q : ℝ) ≤ Real.log ((q + 2 : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      push_cast
      linarith
    push_cast at hmono ⊢
    linarith
  · set p : ℕ := r.num.natAbs with hpdef
    set m : ℕ := r.den with hmdef
    have hmpos : 0 < m := r.pos
    have hnum : (0 : ℤ) < r.num := Rat.num_pos.mpr hpos
    have hppos : 0 < p := Int.natAbs_pos.mpr hnum.ne'
    have hkappa : easyRectKappa p m = (r : ℝ) := easyRectKappa_num_den hpos
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have hple : p ≤ m := by
      have h1 : ((r : ℝ)) ≤ 1 := by exact_mod_cast hr₁
      rw [← hkappa] at h1
      rw [show easyRectKappa p m = (p : ℝ) / (m : ℝ) from rfl, div_le_one hmR] at h1
      exact_mod_cast h1
    have hΛ : easyRectFiberExponent p m = 2 * m := by
      unfold easyRectFiberExponent
      omega
    have hbound := easyRect_rectangularOmega_le_huangPan K q p m hq hppos hmpos
    rw [hkappa, hΛ] at hbound
    have h4 : (2 : ℝ) ^ (((2 * m : ℕ) : ℝ) / (m : ℝ)) = 4 := by
      have hexp : (((2 * m : ℕ)) : ℝ) / (m : ℝ) = ((2 : ℕ) : ℝ) := by
        push_cast
        field_simp
      rw [hexp, Real.rpow_natCast]
      norm_num
    rw [h4] at hbound
    exact hbound

/-- **The `r ≥ 1` branch of Huang--Pan Section 6, in the whole-fiber form.**

`ω(1, 1, r) ≤ log (2^(1+r) · r^r · (q+2)^(2+r) / (2+r)^(2+r)) / log q`.

Huang--Pan's (6.1) has the smaller factor `((1+r)N; N, rN)^{1/N} = (1+r)^(1+r)/r^r` in place of
`2^(1+r)`; the two coincide exactly at `r = 1`.  The sharp form is
`huangPan_rectangularOmega_le_of_one_le_sharp` in
`Examples/CoppersmithWinogradEasyRectangularSharpBound.lean`; this statement is the whole-fiber
one, obtained without any binomial entropy estimate. -/
theorem huangPan_rectangularOmega_le_of_one_le (q : ℕ) (hq : 1 < q) {r : ℚ} (hr : 1 ≤ r) :
    rectangularOmega K ((r : ℝ)) ≤
      Real.log ((2 : ℝ) ^ (1 + (r : ℝ)) * (r : ℝ) ^ ((r : ℝ))
        * ((q + 2 : ℕ) : ℝ) ^ (2 + (r : ℝ))
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
  have hΛ : easyRectFiberExponent p m = p + m := by
    unfold easyRectFiberExponent
    omega
  have hbound := easyRect_rectangularOmega_le_huangPan K q p m hq hppos hmpos
  rw [hΛ] at hbound
  have hexp : (((p + m : ℕ)) : ℝ) / (m : ℝ) = 1 + easyRectKappa p m := by
    rw [show easyRectKappa p m = (p : ℝ) / (m : ℝ) from rfl]
    push_cast
    field_simp
    ring
  rw [hexp, hkappa] at hbound
  exact hbound

end Branches

/-! ## Faithfulness at `r = 1` -/

/-- At `r = 1` the Huang--Pan expression is the equal-type constant `(4/27)·(q+2)^3` of
`easyCW_omega_le_log`. -/
theorem huangPan_bound_one_eq_easyCW (q : ℕ) :
    (4 : ℝ) * (((1 : ℚ) : ℝ)) ^ (((1 : ℚ) : ℝ)) * ((q + 2 : ℕ) : ℝ) ^ (2 + (((1 : ℚ) : ℝ)))
        / (2 + (((1 : ℚ) : ℝ))) ^ (2 + (((1 : ℚ) : ℝ)))
      = (4 / 27 : ℝ) * (((q + 2 : ℕ) : ℝ) ^ 3) := by
  have h1 : (((1 : ℚ) : ℝ)) = (1 : ℝ) := by norm_num
  have e3 : (2 : ℝ) + (1 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  have h27 : (((3 : ℕ) : ℝ)) ^ (3 : ℕ) = 27 := by norm_num
  rw [h1, Real.one_rpow, e3, Real.rpow_natCast, Real.rpow_natCast, h27]
  ring

/-- The `r ≥ 1` branch has the same value at `r = 1`. -/
theorem huangPan_upperBranch_one_eq_easyCW (q : ℕ) :
    (2 : ℝ) ^ (1 + (((1 : ℚ) : ℝ))) * (((1 : ℚ) : ℝ)) ^ (((1 : ℚ) : ℝ))
        * ((q + 2 : ℕ) : ℝ) ^ (2 + (((1 : ℚ) : ℝ)))
        / (2 + (((1 : ℚ) : ℝ))) ^ (2 + (((1 : ℚ) : ℝ)))
      = (4 / 27 : ℝ) * (((q + 2 : ℕ) : ℝ) ^ 3) := by
  have h1 : (((1 : ℚ) : ℝ)) = (1 : ℝ) := by norm_num
  have e2 : (1 : ℝ) + (1 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  have e3 : (2 : ℝ) + (1 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  have h27 : (((3 : ℕ) : ℝ)) ^ (3 : ℕ) = 27 := by norm_num
  have h4 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
  rw [h1, Real.one_rpow, e2, e3, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast,
    h27, h4]
  ring

/-- **Faithfulness check.**  At `r = 1` the rectangular theorem is, as a statement, exactly the
equal-type theorem `easyCW_omega_le_log` of `Examples/CoppersmithWinogradEasyHashing.lean`. -/
theorem huangPan_rectangularOmega_le_one_eq_easyCW (K : Type u) [Field K] (q : ℕ) :
    (rectangularOmega K (((1 : ℚ) : ℝ)) ≤
        Real.log (4 * (((1 : ℚ) : ℝ)) ^ (((1 : ℚ) : ℝ))
          * ((q + 2 : ℕ) : ℝ) ^ (2 + (((1 : ℚ) : ℝ)))
          / (2 + (((1 : ℚ) : ℝ))) ^ (2 + (((1 : ℚ) : ℝ)))) / Real.log q) ↔
      (omega K ≤ Real.log ((4 / 27 : ℝ) * (((q + 2 : ℕ) : ℝ) ^ 3)) / Real.log q) := by
  rw [huangPan_bound_one_eq_easyCW q, show (((1 : ℚ) : ℝ)) = (1 : ℝ) from by norm_num,
    rectangularOmega_one]

end AlgebraicComplexity.Examples
