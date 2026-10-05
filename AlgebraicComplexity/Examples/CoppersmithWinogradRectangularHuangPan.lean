/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRectangularBound

/-!
# Huang--Pan (7.1) and (7.2) in the paper's `(r, β)` variables

`Examples/CoppersmithWinogradRectangularBound.lean` proves the rectangular bound in the
denominator-free profile variables `(p, m, u, v)`:

```text
ω(1,1,p/m) ≤ (T log (q+2) - T log T + u log u + (p+m) log (p+m) + (m+u+v) log (m+u+v))
             / (m log q),        T = p + 2m + 2u + v.
```

Huang and Pan write the same statement in the two scale-free parameters
`r = p/m` (the aspect ratio) and `β = L/N` (the corner fraction), [HP98, (7.1) on p. 277]:

```text
ω(1,1,r) ≤ log (β^β · ((1+r)(1-β))^{(1+r)(1-β)} · (1+rβ)^{1+rβ} · (q+2)^{2+r} / (2+r)^{2+r})
           / ((1-β) log q).
```

This module proves that the two are the same inequality.  With `N = m + u` one has

```text
β = u/N,   1 - β = m/N,   2 + r = T/N,   (1+r)(1-β) = (p+m)/N,   1 + rβ = (m+u+v)/N,
```

the last two using Huang--Pan's proportionality `v/u = p/m` (their `f = rL`), which is the
hypothesis `m * v = p * u` below.  Because `u + (p+m) + (m+u+v) = T`, every `log N` cancels and the
`(r, β)` numerator is exactly `1/N` times the profile numerator, while the `(r, β)` denominator is
`1/N` times `m log q`.

## Main results

* `cwRectBeta` -- Huang--Pan's `β = L/N = u/(m+u)`;
* `huangPan_fullTensor_rectangularOmega_le` -- **(7.1)** verbatim, over every field;
* `huangPan_fullTensor_rectangularOmega_le_of_le_one` -- **(7.2)** verbatim, the `r ≤ 1` branch,
  where the `x`-leg competitor count is the larger one;
* `huangPan_fullTensor_bracket_one_eq` -- the check that the two brackets agree at `r = 1`;
* `huangPan_fullTensor_rectangularOmega_two_lt` -- its `r = 2` instance, `ω(1,1,2) < 3.334`
  ([HP98, Section 5, p. 271]);
* `huangPan_fullTensor_two_profile`, `huangPan_fullTensor_one_profile` -- the two certified
  profiles really are `(r, β) = (2, 1/64)` and `(r, β) = (1, 1/21)`.

## References

* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299; (7.1) on p. 277, (7.2) on p. 278, and Section 5 on
  p. 271.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Huang--Pan's corner fraction `β = L/N`.  In the profile variables `N = m + u` is the number of
non-corner-plus-corner factors per unit, and `u` is the corner count, so `β = u/(m+u)`. -/
noncomputable def cwRectBeta (m u : ℕ) : ℝ := (u : ℝ) / ((m + u : ℕ) : ℝ)

theorem cwRectBeta_pos {m u : ℕ} (hu : 0 < u) : 0 < cwRectBeta m u := by
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hnR : (0 : ℝ) < ((m + u : ℕ) : ℝ) := by
    have : 0 < m + u := by omega
    exact_mod_cast this
  unfold cwRectBeta
  positivity

theorem cwRectBeta_lt_one {m u : ℕ} (hm : 0 < m) : cwRectBeta m u < 1 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < ((m + u : ℕ) : ℝ) := by
    have : 0 < m + u := by omega
    exact_mod_cast this
  unfold cwRectBeta
  rw [div_lt_one hnR]
  push_cast
  linarith

section HuangPan

variable (K : Type u) [Field K]

/-- **Huang--Pan (7.1)** [HP98, p. 277].  For every field, every `q > 1`, and every profile
`(p, m, u, v)` with `m ≤ p` (their `r ≥ 1`), `2u ≤ m` (their `β ≤ 1/3`), `u ≤ v`, and the
proportionality `m·v = p·u` (their `f = rL`),

```text
ω(1,1,r) ≤ log (β^β · ((1+r)(1-β))^{(1+r)(1-β)} · (1+rβ)^{1+rβ} · (q+2)^{2+r} / (2+r)^{2+r})
           / ((1-β) log q)
```

with `r = p/m` and `β = u/(m+u)`, and all displayed powers read as `Real.rpow`. -/
theorem huangPan_fullTensor_rectangularOmega_le (q p m u v : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) (hu : 0 < u) (hv : 0 < v)
    (hmp : m ≤ p) (h2u : 2 * u ≤ m) (huv : u ≤ v) (hprop : m * v = p * u) :
    rectangularOmega K (cwRectKappa p m) ≤
      Real.log (cwRectBeta m u ^ cwRectBeta m u
          * ((1 + cwRectKappa p m) * (1 - cwRectBeta m u)) ^
              ((1 + cwRectKappa p m) * (1 - cwRectBeta m u))
          * (1 + cwRectKappa p m * cwRectBeta m u) ^
              (1 + cwRectKappa p m * cwRectBeta m u)
          * ((q + 2 : ℕ) : ℝ) ^ (2 + cwRectKappa p m)
          / (2 + cwRectKappa p m) ^ (2 + cwRectKappa p m))
        / ((1 - cwRectBeta m u) * Real.log q) := by
  -- Real shadows of the profile.
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hnR : (0 : ℝ) < ((m + u : ℕ) : ℝ) := by
    have : 0 < m + u := by omega
    exact_mod_cast this
  have hTR : (0 : ℝ) < ((p + 2 * m + 2 * u + v : ℕ) : ℝ) := by
    have : 0 < p + 2 * m + 2 * u + v := by omega
    exact_mod_cast this
  have hPMR : (0 : ℝ) < ((p + m : ℕ) : ℝ) := by
    have : 0 < p + m := by omega
    exact_mod_cast this
  have hSR : (0 : ℝ) < ((m + u + v : ℕ) : ℝ) := by
    have : 0 < m + u + v := by omega
    exact_mod_cast this
  have hQR : (0 : ℝ) < ((q + 2 : ℕ) : ℝ) := by
    have : 0 < q + 2 := by omega
    exact_mod_cast this
  have hpropR : (m : ℝ) * (v : ℝ) = (p : ℝ) * (u : ℝ) := by exact_mod_cast hprop
  have hncast : ((m + u : ℕ) : ℝ) = (m : ℝ) + (u : ℝ) := by push_cast; ring
  have hTcast : ((p + 2 * m + 2 * u + v : ℕ) : ℝ) =
      (p : ℝ) + 2 * (m : ℝ) + 2 * (u : ℝ) + (v : ℝ) := by push_cast; ring
  have hPMcast : ((p + m : ℕ) : ℝ) = (p : ℝ) + (m : ℝ) := by push_cast; ring
  have hScast : ((m + u + v : ℕ) : ℝ) = (m : ℝ) + (u : ℝ) + (v : ℝ) := by push_cast; ring
  set nR : ℝ := ((m + u : ℕ) : ℝ) with hnRdef
  set TR : ℝ := ((p + 2 * m + 2 * u + v : ℕ) : ℝ) with hTRdef
  set PMR : ℝ := ((p + m : ℕ) : ℝ) with hPMRdef
  set SR : ℝ := ((m + u + v : ℕ) : ℝ) with hSRdef
  set QR : ℝ := ((q + 2 : ℕ) : ℝ) with hQRdef
  set r : ℝ := cwRectKappa p m with hrdef
  set β : ℝ := cwRectBeta m u with hβdef
  -- The five scale-free identities.
  have hβval : β = (u : ℝ) / nR := rfl
  have hrval : r = (p : ℝ) / (m : ℝ) := rfl
  have hmune : ((m : ℝ) + (u : ℝ)) ≠ 0 := ne_of_gt (by linarith)
  have h1β : 1 - β = (m : ℝ) / nR := by
    rw [hβval, hncast]
    field_simp
    ring
  have hA : (1 + r) * (1 - β) = PMR / nR := by
    rw [h1β, hrval, hPMcast, hncast]
    field_simp
    ring
  have hB : 1 + r * β = SR / nR := by
    rw [hβval, hrval, hScast, hncast]
    field_simp
    nlinarith [hpropR]
  have hS2 : 2 + r = TR / nR := by
    rw [hrval, hTcast, hncast]
    field_simp
    nlinarith [hpropR]
  -- Positivity of the four bases.
  have hβpos : 0 < β := cwRectBeta_pos hu
  have hApos : 0 < (1 + r) * (1 - β) := by rw [hA]; positivity
  have hBpos : 0 < 1 + r * β := by rw [hB]; positivity
  have hS2pos : 0 < 2 + r := by rw [hS2]; positivity
  -- Expand the logarithm of the Huang--Pan bracket.
  have hlogBIG :
      Real.log (β ^ β * ((1 + r) * (1 - β)) ^ ((1 + r) * (1 - β))
          * (1 + r * β) ^ (1 + r * β) * QR ^ (2 + r) / (2 + r) ^ (2 + r)) =
        β * Real.log β + ((1 + r) * (1 - β)) * Real.log ((1 + r) * (1 - β))
          + (1 + r * β) * Real.log (1 + r * β) + (2 + r) * Real.log QR
          - (2 + r) * Real.log (2 + r) := by
    have e1 : (0 : ℝ) < β ^ β := Real.rpow_pos_of_pos hβpos _
    have e2 : (0 : ℝ) < ((1 + r) * (1 - β)) ^ ((1 + r) * (1 - β)) :=
      Real.rpow_pos_of_pos hApos _
    have e3 : (0 : ℝ) < (1 + r * β) ^ (1 + r * β) := Real.rpow_pos_of_pos hBpos _
    have e4 : (0 : ℝ) < QR ^ (2 + r) := Real.rpow_pos_of_pos hQR _
    have e5 : (0 : ℝ) < (2 + r) ^ (2 + r) := Real.rpow_pos_of_pos hS2pos _
    rw [Real.log_div (by positivity) e5.ne',
      Real.log_mul (by positivity) e4.ne',
      Real.log_mul (by positivity) e3.ne',
      Real.log_mul e1.ne' e2.ne',
      Real.log_rpow hβpos, Real.log_rpow hApos, Real.log_rpow hBpos, Real.log_rpow hQR,
      Real.log_rpow hS2pos]
  -- Rewrite each factor as `X / N` and cancel the `log N` terms.
  have hsum : (u : ℝ) + PMR + SR = TR := by
    rw [hPMcast, hScast, hTcast]
    ring
  have hlogβ : Real.log β = Real.log (u : ℝ) - Real.log nR := by
    rw [hβval, Real.log_div huR.ne' hnR.ne']
  have hlogA : Real.log ((1 + r) * (1 - β)) = Real.log PMR - Real.log nR := by
    rw [hA, Real.log_div hPMR.ne' hnR.ne']
  have hlogB : Real.log (1 + r * β) = Real.log SR - Real.log nR := by
    rw [hB, Real.log_div hSR.ne' hnR.ne']
  have hlogS2 : Real.log (2 + r) = Real.log TR - Real.log nR := by
    rw [hS2, Real.log_div hTR.ne' hnR.ne']
  have hnum :
      Real.log (β ^ β * ((1 + r) * (1 - β)) ^ ((1 + r) * (1 - β))
          * (1 + r * β) ^ (1 + r * β) * QR ^ (2 + r) / (2 + r) ^ (2 + r)) =
        (TR * Real.log QR - TR * Real.log TR + (u : ℝ) * Real.log (u : ℝ)
          + PMR * Real.log PMR + SR * Real.log SR) / nR := by
    rw [hlogBIG, hlogβ, hlogA, hlogB, hlogS2, hA, hB, hS2, hβval, ← hsum]
    field_simp
    ring
  -- Assemble.
  have hbound := cwRect_rectangularOmega_le_log K q p m u v hq hp hm hu hv hmp h2u huv
  refine hbound.trans (le_of_eq ?_)
  rw [hnum, h1β]
  have hlq : Real.log (q : ℝ) ≠ 0 := by
    have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact (Real.log_pos hqR).ne'
  field_simp
  ring

end HuangPan

/-! ## Huang--Pan (7.2), the `r ≤ 1` branch -/

section HuangPanLow

variable (K : Type u) [Field K]

/-- **Huang--Pan (7.2)** [HP98, p. 278].  For every field, every `q > 1`, and every profile
`(p, m, u, v)` with `p ≤ m` (their `0 ≤ r ≤ 1`), `2u ≤ m` (their `β ≤ 1/3`), `v ≤ u`, and the
proportionality `m·v = p·u` (their `f = rL`),

```text
ω(1,1,r) ≤ log ((rβ)^{rβ} · (2(1-β))^{2(1-β)} · (r(1-β)+2β)^{r(1-β)+2β} · (q+2)^{2+r}
                / (2+r)^{2+r})
           / ((1-β) log q)
```

with `r = p/m` and `β = u/(m+u)`, and all displayed powers read as `Real.rpow`.

This is `huangPan_fullTensor_rectangularOmega_le` with the leg selection reversed: the competitor
count is the `x`-leg fiber (`cwRectTypedFiberBound_eq_X`) rather than the `y`-leg one. -/
theorem huangPan_fullTensor_rectangularOmega_le_of_le_one (q p m u v : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) (hu : 0 < u) (hv : 0 < v)
    (hpm : p ≤ m) (h2u : 2 * u ≤ m) (hvu : v ≤ u) (hprop : m * v = p * u) :
    rectangularOmega K (cwRectKappa p m) ≤
      Real.log ((cwRectKappa p m * cwRectBeta m u) ^ (cwRectKappa p m * cwRectBeta m u)
          * (2 * (1 - cwRectBeta m u)) ^ (2 * (1 - cwRectBeta m u))
          * (cwRectKappa p m * (1 - cwRectBeta m u) + 2 * cwRectBeta m u) ^
              (cwRectKappa p m * (1 - cwRectBeta m u) + 2 * cwRectBeta m u)
          * ((q + 2 : ℕ) : ℝ) ^ (2 + cwRectKappa p m)
          / (2 + cwRectKappa p m) ^ (2 + cwRectKappa p m))
        / ((1 - cwRectBeta m u) * Real.log q) := by
  -- Real shadows of the profile.
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hnR : (0 : ℝ) < ((m + u : ℕ) : ℝ) := by
    have : 0 < m + u := by omega
    exact_mod_cast this
  have hTR : (0 : ℝ) < ((p + 2 * m + 2 * u + v : ℕ) : ℝ) := by
    have : 0 < p + 2 * m + 2 * u + v := by omega
    exact_mod_cast this
  have h2MR : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by
    have : 0 < 2 * m := by omega
    exact_mod_cast this
  have hP2UR : (0 : ℝ) < ((p + 2 * u : ℕ) : ℝ) := by
    have : 0 < p + 2 * u := by omega
    exact_mod_cast this
  have hQR : (0 : ℝ) < ((q + 2 : ℕ) : ℝ) := by
    have : 0 < q + 2 := by omega
    exact_mod_cast this
  have hpropR : (m : ℝ) * (v : ℝ) = (p : ℝ) * (u : ℝ) := by exact_mod_cast hprop
  have hncast : ((m + u : ℕ) : ℝ) = (m : ℝ) + (u : ℝ) := by push_cast; ring
  have hTcast : ((p + 2 * m + 2 * u + v : ℕ) : ℝ) =
      (p : ℝ) + 2 * (m : ℝ) + 2 * (u : ℝ) + (v : ℝ) := by push_cast; ring
  have h2Mcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have hP2Ucast : ((p + 2 * u : ℕ) : ℝ) = (p : ℝ) + 2 * (u : ℝ) := by push_cast; ring
  set nR : ℝ := ((m + u : ℕ) : ℝ) with hnRdef
  set TR : ℝ := ((p + 2 * m + 2 * u + v : ℕ) : ℝ) with hTRdef
  set MMR : ℝ := ((2 * m : ℕ) : ℝ) with hMMRdef
  set PUR : ℝ := ((p + 2 * u : ℕ) : ℝ) with hPURdef
  set QR : ℝ := ((q + 2 : ℕ) : ℝ) with hQRdef
  set r : ℝ := cwRectKappa p m with hrdef
  set β : ℝ := cwRectBeta m u with hβdef
  -- The four scale-free identities.
  have hβval : β = (u : ℝ) / nR := rfl
  have hrval : r = (p : ℝ) / (m : ℝ) := rfl
  have h1β : 1 - β = (m : ℝ) / nR := by
    rw [hβval, hncast]
    field_simp
    ring
  have hA : r * β = (v : ℝ) / nR := by
    rw [hβval, hrval, hncast]
    field_simp
    nlinarith [hpropR]
  have hB : 2 * (1 - β) = MMR / nR := by
    rw [h1β, h2Mcast, hncast]
    field_simp
  have hC : r * (1 - β) + 2 * β = PUR / nR := by
    rw [h1β, hβval, hrval, hP2Ucast, hncast]
    field_simp
  have hS2 : 2 + r = TR / nR := by
    rw [hrval, hTcast, hncast]
    field_simp
    nlinarith [hpropR]
  -- Positivity of the four bases.
  have hApos : 0 < r * β := by rw [hA]; positivity
  have hBpos : 0 < 2 * (1 - β) := by rw [hB]; positivity
  have hCpos : 0 < r * (1 - β) + 2 * β := by rw [hC]; positivity
  have hS2pos : 0 < 2 + r := by rw [hS2]; positivity
  -- Expand the logarithm of the Huang--Pan bracket.
  have hlogBIG :
      Real.log ((r * β) ^ (r * β) * (2 * (1 - β)) ^ (2 * (1 - β))
          * (r * (1 - β) + 2 * β) ^ (r * (1 - β) + 2 * β) * QR ^ (2 + r)
          / (2 + r) ^ (2 + r)) =
        (r * β) * Real.log (r * β) + (2 * (1 - β)) * Real.log (2 * (1 - β))
          + (r * (1 - β) + 2 * β) * Real.log (r * (1 - β) + 2 * β) + (2 + r) * Real.log QR
          - (2 + r) * Real.log (2 + r) := by
    have e1 : (0 : ℝ) < (r * β) ^ (r * β) := Real.rpow_pos_of_pos hApos _
    have e2 : (0 : ℝ) < (2 * (1 - β)) ^ (2 * (1 - β)) := Real.rpow_pos_of_pos hBpos _
    have e3 : (0 : ℝ) < (r * (1 - β) + 2 * β) ^ (r * (1 - β) + 2 * β) :=
      Real.rpow_pos_of_pos hCpos _
    have e4 : (0 : ℝ) < QR ^ (2 + r) := Real.rpow_pos_of_pos hQR _
    have e5 : (0 : ℝ) < (2 + r) ^ (2 + r) := Real.rpow_pos_of_pos hS2pos _
    rw [Real.log_div (by positivity) e5.ne',
      Real.log_mul (by positivity) e4.ne',
      Real.log_mul (by positivity) e3.ne',
      Real.log_mul e1.ne' e2.ne',
      Real.log_rpow hApos, Real.log_rpow hBpos, Real.log_rpow hCpos, Real.log_rpow hQR,
      Real.log_rpow hS2pos]
  -- Rewrite each factor as `X / N` and cancel the `log N` terms.
  have hsum : (v : ℝ) + MMR + PUR = TR := by
    rw [h2Mcast, hP2Ucast, hTcast]
    ring
  have hlogA : Real.log (r * β) = Real.log (v : ℝ) - Real.log nR := by
    rw [hA, Real.log_div hvR.ne' hnR.ne']
  have hlogB : Real.log (2 * (1 - β)) = Real.log MMR - Real.log nR := by
    rw [hB, Real.log_div h2MR.ne' hnR.ne']
  have hlogC : Real.log (r * (1 - β) + 2 * β) = Real.log PUR - Real.log nR := by
    rw [hC, Real.log_div hP2UR.ne' hnR.ne']
  have hlogS2 : Real.log (2 + r) = Real.log TR - Real.log nR := by
    rw [hS2, Real.log_div hTR.ne' hnR.ne']
  have hnum :
      Real.log ((r * β) ^ (r * β) * (2 * (1 - β)) ^ (2 * (1 - β))
          * (r * (1 - β) + 2 * β) ^ (r * (1 - β) + 2 * β) * QR ^ (2 + r)
          / (2 + r) ^ (2 + r)) =
        (TR * Real.log QR - TR * Real.log TR + (v : ℝ) * Real.log (v : ℝ)
          + MMR * Real.log MMR + PUR * Real.log PUR) / nR := by
    rw [hlogBIG, hlogA, hlogB, hlogC, hlogS2, hA, hB, hC, hS2, ← hsum]
    field_simp
    ring
  -- Assemble.
  have hbound := cwRect_rectangularOmega_le_log_of_le_one K q p m u v hq hp hm hu hv hpm h2u hvu
  refine hbound.trans (le_of_eq ?_)
  rw [hnum, h1β]
  have hlq : Real.log (q : ℝ) ≠ 0 := by
    have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact (Real.log_pos hqR).ne'
  field_simp
  ring

end HuangPanLow

/-! ## The two branches at `r = 1` -/

/-- **The brackets of (7.1) and (7.2) agree at `r = 1`.**  Setting `r = 1` in the bracket of (7.2)
gives `β^β · (2(1-β))^{2(1-β)} · (1+β)^{1+β}`, which is the bracket of (7.1) at `r = 1`; the
denominators `(1-β) log q` are identical.  So the two branches of Huang--Pan's Section 7 meet on
the square case, as they must -- there the two leg fibers are literally equal
(`cwRectLegTypedFiber_firstPower_eq`, `cwRectSharpFiberGrowthX_self`). -/
theorem huangPan_fullTensor_bracket_one_eq (Q β : ℝ) :
    ((1 : ℝ) * β) ^ ((1 : ℝ) * β)
        * (2 * (1 - β)) ^ (2 * (1 - β))
        * ((1 : ℝ) * (1 - β) + 2 * β) ^ ((1 : ℝ) * (1 - β) + 2 * β)
        * Q ^ (2 + (1 : ℝ)) / (2 + (1 : ℝ)) ^ (2 + (1 : ℝ))
      = β ^ β * ((1 + (1 : ℝ)) * (1 - β)) ^ ((1 + (1 : ℝ)) * (1 - β))
        * (1 + (1 : ℝ) * β) ^ (1 + (1 : ℝ) * β)
        * Q ^ (2 + (1 : ℝ)) / (2 + (1 : ℝ)) ^ (2 + (1 : ℝ)) := by
  have e1 : (1 : ℝ) * β = β := one_mul β
  have e2 : (1 : ℝ) * (1 - β) + 2 * β = 1 + β := by ring
  have e3 : (1 : ℝ) + (1 : ℝ) = 2 := by norm_num
  rw [e1, e2, e3]

/-! ## The `r = 2` instance -/

section Numeric

variable (K : Type u) [Field K]

/-- **`ω(1,1,2) < 3.334`** in the `(r, β)` form of Huang--Pan Section 5 (p. 271).  This is
`cwRect_rectangularOmega_two_lt` restated through `huangPan_fullTensor_rectangularOmega_le`; the
profile is `q = 9`, `(p, m, u, v) = (126, 63, 1, 2)`, that is `r = 2` and `β = 1/64`. -/
theorem huangPan_fullTensor_rectangularOmega_two_lt : rectangularOmega K 2 < 3.334 :=
  cwRect_rectangularOmega_two_lt K

/-- The Huang--Pan profile used for `ω(1,1,2)` really has `r = 2` and `β = 1/64`. -/
theorem huangPan_fullTensor_two_profile :
    cwRectKappa 126 63 = 2 ∧ cwRectBeta 63 1 = 1 / 64 := by
  constructor
  · unfold cwRectKappa rectAspectRatio; norm_num
  · unfold cwRectBeta; norm_num

/-- The Huang--Pan profile used for the `r = 1` check has `r = 1` and `β = 1/21`. -/
theorem huangPan_fullTensor_one_profile :
    cwRectKappa 80 80 = 1 ∧ cwRectBeta 80 4 = 1 / 21 := by
  constructor
  · unfold cwRectKappa rectAspectRatio; norm_num
  · unfold cwRectBeta; norm_num

end Numeric

end AlgebraicComplexity.Examples
