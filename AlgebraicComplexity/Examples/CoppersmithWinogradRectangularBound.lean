/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.LogConstants
import AlgebraicComplexity.Examples.CoppersmithWinogradRectangularRate

/-!
# Huang--Pan (7.1), (7.2) and `ω(1,1,2) < 3.334`

`Examples/CoppersmithWinogradRectangularRate.lean` ends at the master inequality

`E₀ / Φ · q ^ (m · ω(1,1,p/m)) ≤ (q+2) ^ (p + 2m + 2u + v)`

for *any* geometric envelope `Φ` of the hashing competitor count.  This module supplies the sharp
envelope, reads Huang--Pan (7.1) off the result, and certifies the two headline numbers.

## The sharp envelope

For `m ≤ p`, `2u ≤ m` and `u ≤ v` the largest type-restricted leg fiber is the `y`-leg one
(`cwRectTypedFiberBound_eq_Y`), a product of three binomial coefficients, and along the schedule
`(a,b,e,f) = (pN, mN, uN, vN)` each of them is dominated *exactly*, with no subexponential loss, by
the `N`-th power of a two-letter entropy base
(`Analysis.choose_scaled_le_binomialEntropyBase_pow`).  So

```text
Φ = cwRectSharpFiberGrowth p m u v
  = binomialEntropyBase m (u+v) · binomialEntropyBase u v · binomialEntropyBase p m.
```

Using the loss-free envelope rather than a Stirling estimate keeps the hashing modulus of the
schedule geometric, which is what `Growth.sqrt_log_le_mul_sqrt_succ` needs; a linear-in-`N` loss
in the modulus would have to be absorbed into the base and would degrade the constant past
`3.334`.

Dividing the six-fold multinomial base `E₀` by `Φ` cancels everything except

```text
E₀ / Φ = T^T / (u^u · (p+m)^{p+m} · (m+u+v)^{m+u+v}),      T = p + 2m + 2u + v,
```

which is `WordType.ternaryEntropyBase u (p+m) (m+u+v)`: the entropy base of the *leg marginal*
`(N+rL, (1+r)(N-L), L)` of [HP98, p. 275].  That is exactly the bracket of [HP98, (7.1)]: with
`p = r(1-β)`, `m = 1-β`, `u = β`, `v = rβ` (so that `N = m + u = 1` and `L = β`) one has
`T = 2+r`, `u = β`, `p+m = (1+r)(1-β)` and `m+u+v = 1+rβ`.

## Main results

* `cwRectSharpFiberGrowth`, `cwRectTypedFiberBound_scaled_le_sharp` -- the sharp competitor
  envelope along the Huang--Pan schedule;
* `cwRectSharpGrowth_eq_ternaryEntropyBase` -- the cancellation `E₀/Φ = T^T/(u^u S^S (p+m)^{p+m})`;
* `cwRect_rectangularOmega_le_log` -- **Huang--Pan (7.1)**, denominator-free:

  ```text
  ω(1,1,p/m) ≤ (T log (q+2) - T log T + u log u + (p+m) log (p+m) + (m+u+v) log (m+u+v))
               / (m log q)
  ```

  over every field and for every `q > 1` and every `(p, m, u, v)` with `m ≤ p`, `2u ≤ m`,
  `u ≤ v`;
* `cwRect_rectangularOmega_two_lt` -- **`ω(1,1,2) < 3.334`**, at Huang--Pan's optimum
  `q = 9`, `β = 1/64` ([HP98, Section 5, p. 271], where they report `3.333953…`);
* `cwRect_omega_lt` -- the `r = 1` check: the same machinery gives `ω < 2.3872` at `q = 6`,
  `β = 4/84`, reproducing [CW90, Section 7];
* `cwRect_master_inequality_firstPower` -- the *exact* `r = 1` regression: at
  `(p,m,u,v) = (9519, 9519, 481, 481)` the master inequality is literally
  `cwFirstPower_base_inequality` of
  `Examples/CoppersmithWinogradFirstPowerHashing.lean`;
* `cwRectSharpFiberGrowthX`, `cwRectTypedFiberBound_scaled_le_sharpX`,
  `cwRectSharpGrowthX_eq_ternaryEntropyBase` -- the same three steps for the *`x`*-leg envelope,
  which is the one Huang--Pan select when `r ≤ 1`;
* `cwRect_rectangularOmega_le_log_of_le_one` -- **Huang--Pan (7.2)**, denominator-free:

  ```text
  ω(1,1,p/m) ≤ (T log (q+2) - T log T + v log v + 2m log (2m) + (p+2u) log (p+2u))
               / (m log q)
  ```

  over every field and for every `q > 1` and every `(p, m, u, v)` with `p ≤ m`, `2u ≤ m`,
  `v ≤ u`;
* `cwRectSharpFiberGrowthX_self` -- the two envelopes coincide at `p = m`, `v = u`, so the two
  branches agree at `r = 1`.

## Certified logarithms

The two numerical corollaries reduce to linear inequalities in `log 2, log 3, log 5, log 7` and
`log 11`, all five of them ten-digit named enclosures of `Analysis/LogConstants.lean`.  No
floating-point evaluation and no `native_decide` enters the argument.

## References

* [CW90] D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic progressions*,
  J. Symbolic Comput. **9** (1990), 251--280; Eq. (10) and Section 7.
* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299; Section 5 (p. 271), (7.1) on p. 277 and (7.2) on
  p. 278.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor Growth

universe u

/-! ## The sharp competitor envelope -/

/-- Huang--Pan's sharp competitor growth constant: the product of the three two-letter entropy
bases of the `y`-leg fiber `((N+rL); N-L, L, rL)·(((1+r)(N-L)); N-L, r(N-L))`. -/
noncomputable def cwRectSharpFiberGrowth (p m u v : ℕ) : ℝ :=
  Analysis.binomialEntropyBase m (u + v) * Analysis.binomialEntropyBase u v *
    Analysis.binomialEntropyBase p m

theorem cwRectSharpFiberGrowth_pos {p m u v : ℕ} (hp : 0 < p) (hm : 0 < m) (hu : 0 < u)
    (hv : 0 < v) : 0 < cwRectSharpFiberGrowth p m u v := by
  unfold cwRectSharpFiberGrowth
  exact mul_pos (mul_pos (Analysis.binomialEntropyBase_pos hm (by omega))
    (Analysis.binomialEntropyBase_pos hu hv)) (Analysis.binomialEntropyBase_pos hp hm)

theorem one_le_cwRectSharpFiberGrowth {p m u v : ℕ} (hp : 0 < p) (hm : 0 < m) (hu : 0 < u)
    (hv : 0 < v) : 1 ≤ cwRectSharpFiberGrowth p m u v := by
  unfold cwRectSharpFiberGrowth
  have h1 := Analysis.one_le_binomialEntropyBase hm (show 0 < u + v by omega)
  have h2 := Analysis.one_le_binomialEntropyBase hu hv
  have h3 := Analysis.one_le_binomialEntropyBase hp hm
  have h12 : (1 : ℝ) ≤ Analysis.binomialEntropyBase m (u + v) *
      Analysis.binomialEntropyBase u v := by nlinarith
  nlinarith

/-- **The sharp competitor envelope is exact, with no subexponential loss.**  This is the step
where Huang--Pan's `M ≍ 2·(competitor count) + 1` becomes a geometric sequence in `N`. -/
theorem cwRectTypedFiberBound_scaled_le_sharp {p m u v : ℕ} (hp : 0 < p) (hm : 0 < m)
    (hu : 0 < u) (hv : 0 < v) (hmp : m ≤ p) (h2u : 2 * u ≤ m) (huv : u ≤ v) (N : ℕ) :
    ((cwRectTypedFiberBound (p * N) (m * N) (u * N) (v * N) : ℕ) : ℝ) ≤
      cwRectSharpFiberGrowth p m u v ^ N := by
  have hcollapse : cwRectTypedFiberBound (p * N) (m * N) (u * N) (v * N) =
      cwRectLegTypedFiber (p * N) (m * N) (u * N) (v * N) .Y :=
    cwRectTypedFiberBound_eq_Y (Nat.mul_le_mul_right N hmp)
      (by rw [show 2 * (u * N) = 2 * u * N from by ring]; exact Nat.mul_le_mul_right N h2u)
      (Nat.mul_le_mul_right N huv)
  have hb1 : ((Nat.choose (m * N + u * N + v * N) (m * N) : ℕ) : ℝ) ≤
      Analysis.binomialEntropyBase m (u + v) ^ N := by
    have h := Analysis.choose_scaled_le_binomialEntropyBase_pow (p := m) (m := u + v) hm
      (by omega) N
    rwa [show (m + (u + v)) * N = m * N + u * N + v * N from by ring] at h
  have hb2 : ((Nat.choose (u * N + v * N) (u * N) : ℕ) : ℝ) ≤
      Analysis.binomialEntropyBase u v ^ N := by
    have h := Analysis.choose_scaled_le_binomialEntropyBase_pow (p := u) (m := v) hu hv N
    rwa [show (u + v) * N = u * N + v * N from by ring] at h
  have hb3 : ((Nat.choose (p * N + m * N) (p * N) : ℕ) : ℝ) ≤
      Analysis.binomialEntropyBase p m ^ N := by
    have h := Analysis.choose_scaled_le_binomialEntropyBase_pow (p := p) (m := m) hp hm N
    rwa [show (p + m) * N = p * N + m * N from by ring] at h
  rw [hcollapse]
  have hval : cwRectLegTypedFiber (p * N) (m * N) (u * N) (v * N) .Y =
      Nat.choose (m * N + u * N + v * N) (m * N) * Nat.choose (u * N + v * N) (u * N) *
        Nat.choose (p * N + m * N) (p * N) := rfl
  rw [hval]
  push_cast
  have hnn1 : (0 : ℝ) ≤ ((Nat.choose (m * N + u * N + v * N) (m * N) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hnn2 : (0 : ℝ) ≤ ((Nat.choose (u * N + v * N) (u * N) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnn3 : (0 : ℝ) ≤ ((Nat.choose (p * N + m * N) (p * N) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hE1 : (0 : ℝ) ≤ Analysis.binomialEntropyBase m (u + v) ^ N :=
    pow_nonneg (Analysis.binomialEntropyBase_pos hm (by omega)).le N
  have hE2 : (0 : ℝ) ≤ Analysis.binomialEntropyBase u v ^ N :=
    pow_nonneg (Analysis.binomialEntropyBase_pos hu hv).le N
  unfold cwRectSharpFiberGrowth
  rw [mul_pow, mul_pow]
  exact mul_le_mul (mul_le_mul hb1 hb2 hnn2 hE1) hb3 hnn3 (mul_nonneg hE1 hE2)

/-! ## The cancellation `E₀ / Φ` -/

/-- The ternary entropy base as a plain quotient of powers: the `exp 1` factors cancel. -/
theorem ternaryEntropyBase_eq_pow_div {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    WordType.ternaryEntropyBase a b c =
      ((a + b + c : ℕ) : ℝ) ^ (a + b + c) / ((a : ℝ) ^ a * (b : ℝ) ^ b * (c : ℝ) ^ c) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have heR : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hE : (Real.exp 1) ^ (a + b + c) =
      (Real.exp 1) ^ a * (Real.exp 1) ^ b * (Real.exp 1) ^ c := by
    rw [← pow_add, ← pow_add]
  unfold WordType.ternaryEntropyBase
  rw [div_pow, div_pow, div_pow, div_pow, hE]
  have h1 : ((a : ℝ)) ^ a ≠ 0 := by positivity
  have h2 : ((b : ℝ)) ^ b ≠ 0 := by positivity
  have h3 : ((c : ℝ)) ^ c ≠ 0 := by positivity
  have h4 : (Real.exp 1) ^ a ≠ 0 := by positivity
  have h5 : (Real.exp 1) ^ b ≠ 0 := by positivity
  have h6 : (Real.exp 1) ^ c ≠ 0 := by positivity
  field_simp

/-- **The Huang--Pan cancellation.**  Dividing the six-fold multinomial base by the sharp
competitor envelope leaves the entropy base of the `y`-leg *marginal* type. -/
theorem cwRectSharpGrowth_eq_ternaryEntropyBase {p m u v : ℕ} (hp : 0 < p) (hm : 0 < m)
    (hu : 0 < u) (hv : 0 < v) :
    cwRectEntropyBase p m u v / cwRectSharpFiberGrowth p m u v =
      WordType.ternaryEntropyBase u (p + m) (m + u + v) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hwR : (0 : ℝ) < ((u + v : ℕ) : ℝ) := by
    have : 0 < u + v := by omega
    exact_mod_cast this
  have hSR : (0 : ℝ) < ((m + u + v : ℕ) : ℝ) := by
    have : 0 < m + u + v := by omega
    exact_mod_cast this
  have hPMR : (0 : ℝ) < ((p + m : ℕ) : ℝ) := by
    have : 0 < p + m := by omega
    exact_mod_cast this
  rw [ternaryEntropyBase_eq_pow_div hu (by omega) (by omega)]
  have hsum : u + (p + m) + (m + u + v) = p + 2 * m + 2 * u + v := by omega
  rw [hsum]
  have hassoc : m + (u + v) = m + u + v := by omega
  unfold cwRectEntropyBase cwRectSharpFiberGrowth Analysis.binomialEntropyBase
  rw [hassoc]
  have h2m : ((m : ℝ)) ^ (2 * m) = (m : ℝ) ^ m * (m : ℝ) ^ m := by rw [two_mul, pow_add]
  have h2u : ((u : ℝ)) ^ (2 * u) = (u : ℝ) ^ u * (u : ℝ) ^ u := by rw [two_mul, pow_add]
  rw [h2m, h2u]
  have e1 : ((p : ℝ)) ^ p ≠ 0 := by positivity
  have e2 : ((m : ℝ)) ^ m ≠ 0 := by positivity
  have e3 : ((u : ℝ)) ^ u ≠ 0 := by positivity
  have e4 : ((v : ℝ)) ^ v ≠ 0 := by positivity
  have e5 : (((u + v : ℕ) : ℝ)) ^ (u + v) ≠ 0 := by positivity
  have e6 : (((m + u + v : ℕ) : ℝ)) ^ (m + u + v) ≠ 0 := by positivity
  have e7 : (((p + m : ℕ) : ℝ)) ^ (p + m) ≠ 0 := by positivity
  field_simp

/-- Explicit logarithm of the Huang--Pan growth constant `E₀ / Φ`. -/
theorem log_cwRectSharpGrowth {p m u v : ℕ} (hp : 0 < p) (hm : 0 < m) (hu : 0 < u) (hv : 0 < v) :
    Real.log (cwRectEntropyBase p m u v / cwRectSharpFiberGrowth p m u v) =
      ((p + 2 * m + 2 * u + v : ℕ) : ℝ) * Real.log ((p + 2 * m + 2 * u + v : ℕ) : ℝ)
        - (u : ℝ) * Real.log (u : ℝ)
        - ((p + m : ℕ) : ℝ) * Real.log ((p + m : ℕ) : ℝ)
        - ((m + u + v : ℕ) : ℝ) * Real.log ((m + u + v : ℕ) : ℝ) := by
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hSR : (0 : ℝ) < ((m + u + v : ℕ) : ℝ) := by
    have : 0 < m + u + v := by omega
    exact_mod_cast this
  have hPMR : (0 : ℝ) < ((p + m : ℕ) : ℝ) := by
    have : 0 < p + m := by omega
    exact_mod_cast this
  have hTR : (0 : ℝ) < ((p + 2 * m + 2 * u + v : ℕ) : ℝ) := by
    have : 0 < p + 2 * m + 2 * u + v := by omega
    exact_mod_cast this
  rw [cwRectSharpGrowth_eq_ternaryEntropyBase hp hm hu hv,
    ternaryEntropyBase_eq_pow_div hu (show 0 < p + m by omega) (show 0 < m + u + v by omega),
    show u + (p + m) + (m + u + v) = p + 2 * m + 2 * u + v from by omega]
  have hA : (0 : ℝ) < ((p + 2 * m + 2 * u + v : ℕ) : ℝ) ^ (p + 2 * m + 2 * u + v) :=
    pow_pos hTR _
  have hB : (0 : ℝ) < (u : ℝ) ^ u * ((p + m : ℕ) : ℝ) ^ (p + m) *
      ((m + u + v : ℕ) : ℝ) ^ (m + u + v) := by positivity
  rw [Real.log_div hA.ne' hB.ne']
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-! ## Huang--Pan (7.1) -/

section Bound

variable (K : Type u) [Field K]

/-- **Huang--Pan (7.1), denominator-free.**  For every field, every `q > 1` and every profile
`(p, m, u, v)` with `m ≤ p`, `2u ≤ m` and `u ≤ v`,

```text
ω(1, 1, p/m) ≤ (T log (q+2) - T log T + u log u + (p+m) log (p+m) + (m+u+v) log (m+u+v))
               / (m log q),        T = p + 2m + 2u + v.
```

Substituting `p = r(1-β)`, `m = 1-β`, `u = β`, `v = rβ` turns this into [HP98, (7.1)]

```text
ω(1,1,r) ≤ log (β^β ((1+r)(1-β))^{(1+r)(1-β)} (1+rβ)^{1+rβ} (q+2)^{2+r} / (2+r)^{2+r})
           / ((1-β) log q).
```

The hypotheses `m ≤ p`, `u ≤ v` are Huang--Pan's `r ≥ 1`, and `2u ≤ m` is `β ≤ 1/3`; together they
are what makes their "select the larger former bound" correct
(`cwRectLegTypedFiber_X_le_Y`). -/
theorem cwRect_rectangularOmega_le_log (q p m u v : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) (hu : 0 < u) (hv : 0 < v)
    (hmp : m ≤ p) (h2u : 2 * u ≤ m) (huv : u ≤ v) :
    rectangularOmega K (cwRectKappa p m) ≤
      (((p + 2 * m + 2 * u + v : ℕ) : ℝ) * Real.log ((q + 2 : ℕ) : ℝ)
          - ((p + 2 * m + 2 * u + v : ℕ) : ℝ) *
              Real.log ((p + 2 * m + 2 * u + v : ℕ) : ℝ)
          + (u : ℝ) * Real.log (u : ℝ)
          + ((p + m : ℕ) : ℝ) * Real.log ((p + m : ℕ) : ℝ)
          + ((m + u + v : ℕ) : ℝ) * Real.log ((m + u + v : ℕ) : ℝ))
        / ((m : ℝ) * Real.log q) := by
  have hmaster := cwRect_master_inequality_of_fiberGrowth K q p m u v hq hp hm hu hv
    (one_le_cwRectSharpFiberGrowth hp hm hu hv)
    (cwRectTypedFiberBound_scaled_le_sharp hp hm hu hv hmp h2u huv)
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hGpos : 0 < cwRectEntropyBase p m u v / cwRectSharpFiberGrowth p m u v :=
    div_pos (cwRectEntropyBase_pos hp hm hu hv) (cwRectSharpFiberGrowth_pos hp hm hu hv)
  set ω : ℝ := rectangularOmega K (cwRectKappa p m) with hωdef
  have hYpos : (0 : ℝ) < (q : ℝ) ^ ((m : ℝ) * ω) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hlog := Real.log_le_log (mul_pos hGpos hYpos) hmaster
  rw [Real.log_mul hGpos.ne' hYpos.ne', Real.log_rpow (by linarith), Real.log_pow,
    log_cwRectSharpGrowth hp hm hu hv] at hlog
  rw [le_div_iff₀ (by positivity),
    show ω * ((m : ℝ) * Real.log (q : ℝ)) = ((m : ℝ) * ω) * Real.log (q : ℝ) from by ring]
  push_cast at hlog ⊢
  linarith

end Bound

/-! ## Huang--Pan (7.2), the `r ≤ 1` branch

[HP98, Section 7.2, p. 277--278] runs the *same* schedule, notes that for `0 ≤ r ≤ 1` the two
competitor counts compare the other way,

```text
((1+r)(N-L); N-L, r(N-L)) · ((N+rL); N-L, L, rL)
    < (r(N-L)+2L; r(N-L), L, L) · ((2(N-L)); N-L, N-L),
```

and therefore selects the `x`-leg count instead (`cwRectTypedFiberBound_eq_X`).  Everything else --
the extraction, the hashing, the three losses, the bootstrap -- is untouched, because
`cwRect_master_inequality_of_fiberGrowth` takes the envelope `Φ` as a parameter.

The `x`-leg envelope is again a product of two-letter entropy bases, now

```text
Φ = cwRectSharpFiberGrowthX p m u
  = binomialEntropyBase p (2u) · binomialEntropyBase u u · binomialEntropyBase m m,
```

and the cancellation leaves

```text
E₀ / Φ = T^T / (v^v · (2m)^{2m} · (p+2u)^{p+2u}),      T = p + 2m + 2u + v,
```

which is `WordType.ternaryEntropyBase v (2m) (p+2u)`.  In Huang--Pan's variables (`N = m + u`)
that is `(rβ)^{rβ}`, `(2(1-β))^{2(1-β)}` and `(r(1-β)+2β)^{r(1-β)+2β}`, the bracket of (7.2). -/

/-- The sharp competitor growth constant of the `r ≤ 1` branch: the product of the three
two-letter entropy bases of the `x`-leg fiber
`((r(N-L)+2L); r(N-L), L, L)·((2(N-L)); N-L, N-L)`. -/
noncomputable def cwRectSharpFiberGrowthX (p m u : ℕ) : ℝ :=
  Analysis.binomialEntropyBase p (2 * u) * Analysis.binomialEntropyBase u u *
    Analysis.binomialEntropyBase m m

theorem cwRectSharpFiberGrowthX_pos {p m u : ℕ} (hp : 0 < p) (hm : 0 < m) (hu : 0 < u) :
    0 < cwRectSharpFiberGrowthX p m u := by
  unfold cwRectSharpFiberGrowthX
  exact mul_pos (mul_pos (Analysis.binomialEntropyBase_pos hp (by omega))
    (Analysis.binomialEntropyBase_pos hu hu)) (Analysis.binomialEntropyBase_pos hm hm)

theorem one_le_cwRectSharpFiberGrowthX {p m u : ℕ} (hp : 0 < p) (hm : 0 < m) (hu : 0 < u) :
    1 ≤ cwRectSharpFiberGrowthX p m u := by
  unfold cwRectSharpFiberGrowthX
  have h1 := Analysis.one_le_binomialEntropyBase hp (show 0 < 2 * u by omega)
  have h2 := Analysis.one_le_binomialEntropyBase hu hu
  have h3 := Analysis.one_le_binomialEntropyBase hm hm
  have h12 : (1 : ℝ) ≤ Analysis.binomialEntropyBase p (2 * u) *
      Analysis.binomialEntropyBase u u := by nlinarith
  nlinarith

/-- **The `r ≤ 1` competitor envelope is exact, with no subexponential loss.** -/
theorem cwRectTypedFiberBound_scaled_le_sharpX {p m u v : ℕ} (hp : 0 < p) (hm : 0 < m)
    (hu : 0 < u) (hpm : p ≤ m) (h2u : 2 * u ≤ m) (hvu : v ≤ u) (N : ℕ) :
    ((cwRectTypedFiberBound (p * N) (m * N) (u * N) (v * N) : ℕ) : ℝ) ≤
      cwRectSharpFiberGrowthX p m u ^ N := by
  have hcollapse : cwRectTypedFiberBound (p * N) (m * N) (u * N) (v * N) =
      cwRectLegTypedFiber (p * N) (m * N) (u * N) (v * N) .X :=
    cwRectTypedFiberBound_eq_X (Nat.mul_le_mul_right N hpm)
      (by rw [show 2 * (u * N) = 2 * u * N from by ring]; exact Nat.mul_le_mul_right N h2u)
      (Nat.mul_le_mul_right N hvu)
  have hb1 : ((Nat.choose (p * N + 2 * (u * N)) (p * N) : ℕ) : ℝ) ≤
      Analysis.binomialEntropyBase p (2 * u) ^ N := by
    have h := Analysis.choose_scaled_le_binomialEntropyBase_pow (p := p) (m := 2 * u) hp
      (by omega) N
    rwa [show (p + 2 * u) * N = p * N + 2 * (u * N) from by ring] at h
  have hb2 : ((Nat.choose (2 * (u * N)) (u * N) : ℕ) : ℝ) ≤
      Analysis.binomialEntropyBase u u ^ N := by
    have h := Analysis.choose_scaled_le_binomialEntropyBase_pow (p := u) (m := u) hu hu N
    rwa [show (u + u) * N = 2 * (u * N) from by ring] at h
  have hb3 : ((Nat.choose (2 * (m * N)) (m * N) : ℕ) : ℝ) ≤
      Analysis.binomialEntropyBase m m ^ N := by
    have h := Analysis.choose_scaled_le_binomialEntropyBase_pow (p := m) (m := m) hm hm N
    rwa [show (m + m) * N = 2 * (m * N) from by ring] at h
  rw [hcollapse]
  have hval : cwRectLegTypedFiber (p * N) (m * N) (u * N) (v * N) .X =
      Nat.choose (p * N + 2 * (u * N)) (p * N) * Nat.choose (2 * (u * N)) (u * N) *
        Nat.choose (2 * (m * N)) (m * N) := rfl
  rw [hval]
  push_cast
  have hnn1 : (0 : ℝ) ≤ ((Nat.choose (p * N + 2 * (u * N)) (p * N) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hnn2 : (0 : ℝ) ≤ ((Nat.choose (2 * (u * N)) (u * N) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnn3 : (0 : ℝ) ≤ ((Nat.choose (2 * (m * N)) (m * N) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hE1 : (0 : ℝ) ≤ Analysis.binomialEntropyBase p (2 * u) ^ N :=
    pow_nonneg (Analysis.binomialEntropyBase_pos hp (by omega)).le N
  have hE2 : (0 : ℝ) ≤ Analysis.binomialEntropyBase u u ^ N :=
    pow_nonneg (Analysis.binomialEntropyBase_pos hu hu).le N
  unfold cwRectSharpFiberGrowthX
  rw [mul_pow, mul_pow]
  exact mul_le_mul (mul_le_mul hb1 hb2 hnn2 hE1) hb3 hnn3 (mul_nonneg hE1 hE2)

/-- **The Huang--Pan cancellation in the `r ≤ 1` branch.**  Dividing the six-fold multinomial base
by the `x`-leg envelope leaves the entropy base of the `x`-leg *marginal* type. -/
theorem cwRectSharpGrowthX_eq_ternaryEntropyBase {p m u v : ℕ} (hp : 0 < p) (hm : 0 < m)
    (hu : 0 < u) (hv : 0 < v) :
    cwRectEntropyBase p m u v / cwRectSharpFiberGrowthX p m u =
      WordType.ternaryEntropyBase v (2 * m) (p + 2 * u) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  rw [ternaryEntropyBase_eq_pow_div hv (show 0 < 2 * m by omega) (show 0 < p + 2 * u by omega)]
  rw [show v + 2 * m + (p + 2 * u) = p + 2 * m + 2 * u + v from by omega]
  unfold cwRectEntropyBase cwRectSharpFiberGrowthX Analysis.binomialEntropyBase
  rw [show u + u = 2 * u from by omega, show m + m = 2 * m from by omega]
  have h2m : ((m : ℝ)) ^ (2 * m) = (m : ℝ) ^ m * (m : ℝ) ^ m := by rw [two_mul, pow_add]
  have h2u : ((u : ℝ)) ^ (2 * u) = (u : ℝ) ^ u * (u : ℝ) ^ u := by rw [two_mul, pow_add]
  rw [h2m, h2u]
  have e1 : ((p : ℝ)) ^ p ≠ 0 := by positivity
  have e2 : ((m : ℝ)) ^ m ≠ 0 := by positivity
  have e3 : ((u : ℝ)) ^ u ≠ 0 := by positivity
  have e4 : ((v : ℝ)) ^ v ≠ 0 := by positivity
  have e5 : (((2 * u : ℕ) : ℝ)) ^ (2 * u) ≠ 0 := by positivity
  have e6 : (((2 * m : ℕ) : ℝ)) ^ (2 * m) ≠ 0 := by positivity
  have e7 : (((p + 2 * u : ℕ) : ℝ)) ^ (p + 2 * u) ≠ 0 := by positivity
  field_simp

/-- Explicit logarithm of the `r ≤ 1` growth constant `E₀ / Φ`. -/
theorem log_cwRectSharpGrowthX {p m u v : ℕ} (hp : 0 < p) (hm : 0 < m) (hu : 0 < u) (hv : 0 < v) :
    Real.log (cwRectEntropyBase p m u v / cwRectSharpFiberGrowthX p m u) =
      ((p + 2 * m + 2 * u + v : ℕ) : ℝ) * Real.log ((p + 2 * m + 2 * u + v : ℕ) : ℝ)
        - (v : ℝ) * Real.log (v : ℝ)
        - ((2 * m : ℕ) : ℝ) * Real.log ((2 * m : ℕ) : ℝ)
        - ((p + 2 * u : ℕ) : ℝ) * Real.log ((p + 2 * u : ℕ) : ℝ) := by
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have h2mR : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by
    have : 0 < 2 * m := by omega
    exact_mod_cast this
  have hP2UR : (0 : ℝ) < ((p + 2 * u : ℕ) : ℝ) := by
    have : 0 < p + 2 * u := by omega
    exact_mod_cast this
  have hTR : (0 : ℝ) < ((p + 2 * m + 2 * u + v : ℕ) : ℝ) := by
    have : 0 < p + 2 * m + 2 * u + v := by omega
    exact_mod_cast this
  rw [cwRectSharpGrowthX_eq_ternaryEntropyBase hp hm hu hv,
    ternaryEntropyBase_eq_pow_div hv (show 0 < 2 * m by omega) (show 0 < p + 2 * u by omega),
    show v + 2 * m + (p + 2 * u) = p + 2 * m + 2 * u + v from by omega]
  have hA : (0 : ℝ) < ((p + 2 * m + 2 * u + v : ℕ) : ℝ) ^ (p + 2 * m + 2 * u + v) :=
    pow_pos hTR _
  have hB : (0 : ℝ) < (v : ℝ) ^ v * ((2 * m : ℕ) : ℝ) ^ (2 * m) *
      ((p + 2 * u : ℕ) : ℝ) ^ (p + 2 * u) := by positivity
  rw [Real.log_div hA.ne' hB.ne']
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

section BoundLow

variable (K : Type u) [Field K]

/-- **Huang--Pan (7.2), denominator-free.**  For every field, every `q > 1` and every profile
`(p, m, u, v)` with `p ≤ m`, `2u ≤ m` and `v ≤ u`,

```text
ω(1, 1, p/m) ≤ (T log (q+2) - T log T + v log v + 2m log (2m) + (p+2u) log (p+2u))
               / (m log q),        T = p + 2m + 2u + v.
```

Substituting `p = r(1-β)`, `m = 1-β`, `u = β`, `v = rβ` turns this into [HP98, (7.2)]

```text
ω(1,1,r) ≤ log ((rβ)^{rβ} (2(1-β))^{2(1-β)} (r(1-β)+2β)^{r(1-β)+2β} (q+2)^{2+r} / (2+r)^{2+r})
           / ((1-β) log q).
```

The hypotheses `p ≤ m`, `v ≤ u` are Huang--Pan's `r ≤ 1`, and `2u ≤ m` is `β ≤ 1/3`; together they
reverse their selection of the larger count (`cwRectLegTypedFiber_Y_le_X`). -/
theorem cwRect_rectangularOmega_le_log_of_le_one (q p m u v : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) (hu : 0 < u) (hv : 0 < v)
    (hpm : p ≤ m) (h2u : 2 * u ≤ m) (hvu : v ≤ u) :
    rectangularOmega K (cwRectKappa p m) ≤
      (((p + 2 * m + 2 * u + v : ℕ) : ℝ) * Real.log ((q + 2 : ℕ) : ℝ)
          - ((p + 2 * m + 2 * u + v : ℕ) : ℝ) *
              Real.log ((p + 2 * m + 2 * u + v : ℕ) : ℝ)
          + (v : ℝ) * Real.log (v : ℝ)
          + ((2 * m : ℕ) : ℝ) * Real.log ((2 * m : ℕ) : ℝ)
          + ((p + 2 * u : ℕ) : ℝ) * Real.log ((p + 2 * u : ℕ) : ℝ))
        / ((m : ℝ) * Real.log q) := by
  have hmaster := cwRect_master_inequality_of_fiberGrowth K q p m u v hq hp hm hu hv
    (one_le_cwRectSharpFiberGrowthX hp hm hu)
    (cwRectTypedFiberBound_scaled_le_sharpX hp hm hu hpm h2u hvu)
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hGpos : 0 < cwRectEntropyBase p m u v / cwRectSharpFiberGrowthX p m u :=
    div_pos (cwRectEntropyBase_pos hp hm hu hv) (cwRectSharpFiberGrowthX_pos hp hm hu)
  set ω : ℝ := rectangularOmega K (cwRectKappa p m) with hωdef
  have hYpos : (0 : ℝ) < (q : ℝ) ^ ((m : ℝ) * ω) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hlog := Real.log_le_log (mul_pos hGpos hYpos) hmaster
  rw [Real.log_mul hGpos.ne' hYpos.ne', Real.log_rpow (by linarith), Real.log_pow,
    log_cwRectSharpGrowthX hp hm hu hv] at hlog
  rw [le_div_iff₀ (by positivity),
    show ω * ((m : ℝ) * Real.log (q : ℝ)) = ((m : ℝ) * ω) * Real.log (q : ℝ) from by ring]
  push_cast at hlog ⊢
  linarith

end BoundLow

/-- **The two branches agree at `r = 1`.**  At `p = m` and `v = u` the two leg fibers coincide
(`cwRectLegTypedFiber_firstPower_eq`), and so do the two envelopes; the `r ≥ 1` bound
`cwRect_rectangularOmega_le_log` and the `r ≤ 1` bound `cwRect_rectangularOmega_le_log_of_le_one`
are then the same inequality. -/
theorem cwRectSharpFiberGrowthX_self (m u : ℕ) :
    cwRectSharpFiberGrowthX m m u = cwRectSharpFiberGrowth m m u u := by
  unfold cwRectSharpFiberGrowthX cwRectSharpFiberGrowth
  rw [show u + u = 2 * u from by omega]

/-! ## The `r = 1` regression

At `(p, m, u, v) = (9519, 9519, 481, 481)` -- that is `r = 1`, `β = 481/10000` -- the master
inequality of this pipeline is literally the checked scalar inequality
`cwFirstPower_base_inequality` of `Examples/CoppersmithWinogradFirstPowerHashing.lean`. -/

@[simp] theorem cwRectKappa_self (m : ℕ) (hm : 0 < m) : cwRectKappa m m = 1 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  unfold cwRectKappa rectAspectRatio
  field_simp

/-- The Huang--Pan growth constant at the first-power profile is the checked ternary entropy base
`ternaryEntropyBase 10481 19038 481` of the `ω < 2.3872` client. -/
theorem cwRectSharpGrowth_firstPower :
    cwRectEntropyBase 9519 9519 481 481 / cwRectSharpFiberGrowth 9519 9519 481 481 =
      WordType.ternaryEntropyBase 10481 19038 481 := by
  rw [cwRectSharpGrowth_eq_ternaryEntropyBase (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  rw [ternaryEntropyBase_eq_pow_div (a := 481) (b := 9519 + 9519) (c := 9519 + 481 + 481)
      (by norm_num) (by norm_num) (by norm_num),
    ternaryEntropyBase_eq_pow_div (a := 10481) (b := 19038) (c := 481)
      (by norm_num) (by norm_num) (by norm_num)]
  norm_num
  ring

/-- **Exact `r = 1` regression.**  The rectangular master inequality at the first-power profile is
`cwFirstPower_base_inequality`. -/
theorem cwRect_master_inequality_firstPower (K : Type u) [Field K] (q : ℕ) (hq : 1 < q) :
    WordType.ternaryEntropyBase 10481 19038 481 *
        (q : ℝ) ^ ((9519 : ℝ) * omega K) ≤ ((q + 2 : ℕ) : ℝ) ^ 30000 := by
  have hmaster := cwRect_master_inequality_of_fiberGrowth K q 9519 9519 481 481 hq
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (one_le_cwRectSharpFiberGrowth (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (cwRectTypedFiberBound_scaled_le_sharp (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (le_refl _) (by norm_num) (le_refl _))
  rw [cwRectSharpGrowth_firstPower, cwRectKappa_self 9519 (by norm_num),
    rectangularOmega_one,
    show (9519 + 2 * 9519 + 2 * 481 + 481 : ℕ) = 30000 from by norm_num,
    show ((9519 : ℕ) : ℝ) = (9519 : ℝ) from by norm_num] at hmaster
  exact hmaster

/-! ## The two numerical corollaries -/

section Numeric

variable (K : Type u) [Field K]

/-- **`ω(1,1,2) < 3.334`** -- Huang--Pan's headline bound [HP98, Section 5, p. 271], where they
report `3.333953…`.

The profile is `q = 9`, `(p, m, u, v) = (126, 63, 1, 2)`, i.e. `r = 2` and `β = L/N = 1/64`
(their optimum is `β = 0.016`).  The bound reduces to
`322 log 11 + 189 log 7 + 212.916 log 3 < 1982 log 2`, which the ten-digit enclosures verify with
room to spare. -/
theorem cwRect_rectangularOmega_two_lt : rectangularOmega K 2 < 3.334 := by
  have hkappa : cwRectKappa 126 63 = 2 := by
    unfold cwRectKappa rectAspectRatio
    norm_num
  have h := cwRect_rectangularOmega_le_log K 9 126 63 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hkappa] at h
  refine h.trans_lt ?_
  have e11 : ((9 + 2 : ℕ) : ℝ) = 11 := by norm_num
  have eT : ((126 + 2 * 63 + 2 * 1 + 2 : ℕ) : ℝ) = 256 := by norm_num
  have ePM : ((126 + 63 : ℕ) : ℝ) = 189 := by norm_num
  have eS : ((63 + 1 + 2 : ℕ) : ℝ) = 66 := by norm_num
  have eU : ((1 : ℕ) : ℝ) = 1 := by norm_num
  have eM : ((63 : ℕ) : ℝ) = 63 := by norm_num
  have eQ : ((9 : ℕ) : ℝ) = 9 := by norm_num
  rw [e11, eT, ePM, eS, eU, eM, eQ]
  have l256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 from by norm_num, Real.log_pow]
    push_cast; ring
  have l189 : Real.log 189 = 3 * Real.log 3 + Real.log 7 := by
    rw [show (189 : ℝ) = 3 ^ 3 * 7 from by norm_num,
      Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    push_cast; ring
  have l66 : Real.log 66 = Real.log 2 + Real.log 3 + Real.log 11 := by
    rw [show (66 : ℝ) = 2 * 3 * 11 from by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  have l9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 from by norm_num, Real.log_pow]
    push_cast; ring
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [l256, l189, l66, l9, Real.log_one]
  rw [div_lt_iff₀ (by positivity)]
  linarith [Analysis.log_eleven_le_sharp, Analysis.log_two_ge_sharp, Analysis.log_three_le_sharp,
    Analysis.log_seven_le_sharp]

/-- **`ω < 2.3872`** -- the `r = 1` check that the rectangular machinery reproduces the classical
first-power Coppersmith--Winograd bound of [CW90, Section 7].

The profile is `q = 6`, `(p, m, u, v) = (80, 80, 4, 4)`, i.e. `r = 1` and `β = L/N = 4/84`
(Huang--Pan's `f(1) = 2.38719`).  The bound reduces to
`1133.024 log 2 + 88 log 11 + 160 log 5 < 694.976 log 3 + 252 log 7`. -/
theorem cwRect_omega_lt : omega K < 2.3872 := by
  have hkappa : cwRectKappa 80 80 = 1 := cwRectKappa_self 80 (by norm_num)
  have h := cwRect_rectangularOmega_le_log K 6 80 80 4 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (le_refl _) (by norm_num) (le_refl _)
  rw [hkappa, rectangularOmega_one] at h
  refine h.trans_lt ?_
  have e8 : ((6 + 2 : ℕ) : ℝ) = 8 := by norm_num
  have eT : ((80 + 2 * 80 + 2 * 4 + 4 : ℕ) : ℝ) = 252 := by norm_num
  have ePM : ((80 + 80 : ℕ) : ℝ) = 160 := by norm_num
  have eS : ((80 + 4 + 4 : ℕ) : ℝ) = 88 := by norm_num
  have eU : ((4 : ℕ) : ℝ) = 4 := by norm_num
  have eM : ((80 : ℕ) : ℝ) = 80 := by norm_num
  have eQ : ((6 : ℕ) : ℝ) = 6 := by norm_num
  rw [e8, eT, ePM, eS, eU, eM, eQ]
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, Real.log_pow]
    push_cast; ring
  have l252 : Real.log 252 = 2 * Real.log 2 + 2 * Real.log 3 + Real.log 7 := by
    rw [show (252 : ℝ) = 2 ^ 2 * 3 ^ 2 * 7 from by norm_num,
      Real.log_mul (by positivity) (by norm_num),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
    push_cast; ring
  have l160 : Real.log 160 = 5 * Real.log 2 + Real.log 5 := by
    rw [show (160 : ℝ) = 2 ^ 5 * 5 from by norm_num,
      Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    push_cast; ring
  have l88 : Real.log 88 = 3 * Real.log 2 + Real.log 11 := by
    rw [show (88 : ℝ) = 2 ^ 3 * 11 from by norm_num,
      Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    push_cast; ring
  have l6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 from by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [l8, l252, l4, l160, l88, l6]
  rw [div_lt_iff₀ (by positivity)]
  linarith [Analysis.log_eleven_le_sharp, Analysis.log_two_le_sharp, Analysis.log_three_ge_sharp,
    Analysis.log_five_le_sharp, Analysis.log_seven_ge_sharp]

end Numeric

end AlgebraicComplexity.Examples
