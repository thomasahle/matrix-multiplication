/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradEasyCoordinate
import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinogradBarrier

/-!
# Lower bounds on `Ī` for the generalized Coppersmith--Winograd tensors

Layer 4 (`AlgebraicComplexity/Examples/`).  This module is milestone **M7** of
`BARRIER_FRAMEWORK.md`: [AlmanVassilevskaWilliams2018, Theorem 7.3 and Remark 7.2], the *lower*
bounds on the asymptotic independence number of `CW_q^σ`.  The complementary *upper* bounds --- AVW
Lemmas 7.1 and 7.2 --- are in `Examples/GeneralizedCoppersmithWinogradBarrier.lean`, and the two are
combined here into a single sandwich.

## What is proved, and where the mathematics is

All the mathematics has already happened when this file starts.  Milestone **M6**
(`easyCW_independence_base_inequality`, in `Examples/CoppersmithWinogradEasyCoordinate.lean`) is

```text
(27/4)·q² ≤ Ī(CW_q^σ)³      for every q ≥ 1 and every σ,
```

the coordinate shadow of the three-constituent laser analysis of [CoppersmithWinograd1990, §6] run
through the `F`-copies form of AVW Lemma 4.4 and a Behrend rate limit.  Everything below is real
arithmetic on top of that one inequality: each result is obtained by exhibiting a real number `x`
with `x³ ≤ (27/4)q²` and reading off `x ≤ Ī(CW_q^σ)`
(`le_asymptoticIndependenceNumber_gcwTable_of_cube_le`).

## Main definitions

* `avwF q`, AVW's `f(q) = log_q (4(q+2)³/27)`: the exponent bound of the classical first-power
  Coppersmith--Winograd analysis, `ω ≤ f(q)` (`easyCW_omega_le_log` of
  `Examples/CoppersmithWinogradEasyHashing.lean`).

## Main results

* `avwF_ge_two`: `2 ≤ f(q)` for `q ≥ 2`, equivalent to the polynomial inequality `27q² ≤ 4(q+2)³`.
* `avwF_pos` and `avwF_lt_three`: `0 < f(q)` for `q ≥ 2` and `f(q) < 3` for `q ≥ 3`, the arithmetic
  behind [AlmanVassilevskaWilliams2018, Remark 7.2] and the strict `c_{|G|} > 2/3` of Theorem 7.4.
* `rpow_avwF`: `(q+2)³ = (27/4)·q^{f(q)}`, the defining property of `f`, for `q ≥ 2`.
* `avw_theorem_seven_three` (**AVW Theorem 7.3**): `(q+2)^{2/f(q)} ≤ Ī(CW_q^σ)` for `q ≥ 2`.
* `avw_remark_seven_two` (**AVW Remark 7.2, strengthened**): `(q+2)^{2/3} ≤ Ī(CW_q^σ)` for `q ≥ 2`.
* `avw_gcwTable_independence_sandwich`: Theorem 7.3 together with the corner upper bound
  `Ī(CW_q^σ) ≤ cornerBound (q+2) < q+2` of AVW Lemma 7.1.
* `avw_gcwTable_independence_sandwich_fin_six`: the numeric instance `q = 6`,
  `6.24 ≤ Ī(CW_6^σ) < 8`.

## Errata to [AlmanVassilevskaWilliams2018]

* **`f(1)` is a junk value.**  AVW state Theorem 7.3 for "every positive integer `q`", but
  `f(1) = log(4·3³/27)/log 1 = log 4 / 0` has denominator `Real.log 1 = 0`.  In Lean the quotient
  is the junk value `0`
  and the displayed bound degenerates to `(q+2)^{2/0} = 3^0 = 1`, which is true but empty; the
  underlying inequality `(27/4)·1 ≤ Ī(CW_1^σ)³` (milestone M6) is the meaningful statement at
  `q = 1`.  Every theorem here that mentions `f` therefore assumes `q ≥ 2`.
* **Remark 7.2 holds from `q = 2`.**  AVW state `Ī(CW_q^σ) ≥ (q+2)^{2/3}` for `q ≥ 3`.  The
  inequality it needs, `4(q+2)² ≤ 27q²`, is `23q² − 16q − 16 ≥ 0`, which holds for every `q ≥ 2`
  (at `q = 2` with room: `64 ≤ 108`).  It genuinely fails at `q = 1` (`36 > 27`).
* **AVW's `ω_g(CW_q) ≥ f(q)` is a sign typo** for `≤`: `f(q)` is the exponent *achieved* by the
  first-power analysis.  This is recorded in `BARRIER_FRAMEWORK.md` milestone M and is not used
  here; the only role `f` plays below is as the exponent in AVW's displayed form of Theorem 7.3.

## A deliberate strengthening

The route taken is *not* AVW's.  AVW obtain Theorem 7.3 from a symmetric single-tensor zeroing out
of `CW_q^{⊗n}` into `⟨t,t,t⟩` with `t ≥ (q+2)^{(1−δ)n/f(q)}` (their footnote 9).  Here the
`F`-copies form of Lemma 4.4 is used instead, which needs only *balanced* dimensions and which the
uniform-type extraction of [CoppersmithWinograd1990, §6] already provides.  The resulting M6
inequality `(27/4)q² ≤ Ī³` is strictly stronger than Theorem 7.3: applying
`AlgebraicComplexity.Growth.rpow_two_div_le_of_le_mul_rpow` to `(q+2)³ = (27/4)·q^{f(q)}` with
`f(q) ≥ 2` gives `((q+2)^{2/f(q)})³ ≤ (27/4)q²`, and the gap is real --- at `q = 6` the cube-root
bound is `243^{1/3} = 6.2402…` against AVW's `8^{2/f(6)} = 8^{0.8278…} = 5.5925…`.

## Position in the library

Layer 4.  It imports `Examples/CoppersmithWinogradEasyCoordinate.lean` (milestones M5 and M6) and
`Examples/GeneralizedCoppersmithWinogradBarrier.lean` (milestone K, for the upper half of the
sandwich).  Nothing here is imported by a lower layer.

## References

* [AlmanVassilevskaWilliams2018] J. Alman and V. Vassilevska Williams, *Limits on all known (and
  some unknown) approaches to matrix multiplication*, arXiv:1810.08671; Theorem 7.3, Remark 7.2.
* [CoppersmithWinograd1990] D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic
  progressions*, J. Symbolic Comput. 9 (1990); §6, the three-constituent construction and its
  exponent bound `f(q)`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

section Arithmetic

/-- **AVW's exponent function** `f(q) = log_q (4(q+2)³/27)`, the exponent bound proved by the
three-constituent Coppersmith--Winograd analysis of [CoppersmithWinograd1990, §6]
(`easyCW_omega_le_log`).

The value at `q = 1` is junk: `Real.log 1 = 0`, so `avwF 1 = 0` by Lean's division convention.
[AlmanVassilevskaWilliams2018] state Theorem 7.3 for "every positive integer `q`", but `f` is
undefined at `q = 1`; every result below therefore assumes `q ≥ 2`. -/
noncomputable def avwF (q : ℕ) : ℝ :=
  Real.log ((4 / 27 : ℝ) * ((q + 2 : ℕ) : ℝ) ^ 3) / Real.log q

/-- `2 ≤ f(q)` for every `q ≥ 2`.

Proof sketch: `log q > 0`, so the claim is `log (q²) ≤ log (4(q+2)³/27)`, i.e. the polynomial
inequality `27q² ≤ 4(q+2)³`; expanded, `4q³ − 3q² + 48q + 32 ≥ 0`, which `nlinarith` reads off. -/
theorem avwF_ge_two {q : ℕ} (hq : 2 ≤ q) : 2 ≤ avwF q := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hlog : 0 < Real.log q := Real.log_pos hq1
  rw [avwF, le_div_iff₀ hlog]
  have hsq : (q : ℝ) ^ 2 ≤ (4 / 27 : ℝ) * ((q + 2 : ℕ) : ℝ) ^ 3 := by
    push_cast
    nlinarith [sq_nonneg ((q : ℝ) - 2), sq_nonneg ((q : ℝ) + 2)]
  calc (2 : ℝ) * Real.log q = Real.log ((q : ℝ) ^ 2) := by
        rw [Real.log_pow]; push_cast; ring
    _ ≤ Real.log ((4 / 27 : ℝ) * ((q + 2 : ℕ) : ℝ) ^ 3) :=
        Real.log_le_log (by positivity) hsq

/-- `f(q) > 0` for `q ≥ 2`; immediate from `avwF_ge_two`. -/
theorem avwF_pos {q : ℕ} (hq : 2 ≤ q) : 0 < avwF q :=
  lt_of_lt_of_le (by norm_num) (avwF_ge_two hq)

/-- `f(q) < 3` for every `q ≥ 3`.

This is the inequality behind [AlmanVassilevskaWilliams2018, Remark 7.2] and behind the strict
`c_{|G|} > 2/3` of Theorem 7.4.  It fails at `q = 2`, where `4(q+2)³ = 256 > 216 = 27q³`.

Proof sketch: `log q > 0`, so `f(q) < 3` is `log (4(q+2)³/27) < log (q³)`, i.e. the polynomial
inequality `4(q+2)³ < 27q³`, equivalently `23q³ - 24q² - 48q - 32 > 0`, which holds from `q = 3`
on (`229 > 0` at `q = 3`, and the left side is increasing there). -/
theorem avwF_lt_three {q : ℕ} (hq : 3 ≤ q) : avwF q < 3 := by
  have hq3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hlog : 0 < Real.log q := Real.log_pos hq1
  rw [avwF, div_lt_iff₀ hlog]
  have hcube : (4 / 27 : ℝ) * ((q + 2 : ℕ) : ℝ) ^ 3 < (q : ℝ) ^ 3 := by
    push_cast
    nlinarith [sq_nonneg ((q : ℝ) - 3), sq_nonneg ((q : ℝ) + 3), sq_nonneg ((q : ℝ) - 1)]
  calc Real.log ((4 / 27 : ℝ) * ((q + 2 : ℕ) : ℝ) ^ 3) < Real.log ((q : ℝ) ^ 3) :=
        Real.log_lt_log (by positivity) hcube
    _ = 3 * Real.log q := by rw [Real.log_pow]; push_cast; ring

/-- **The defining property of `f`**: `(q+2)³ = (27/4)·q^{f(q)}` for `q ≥ 2`, the right-hand power
being a real power.

Proof sketch: `q^{f(q)} = exp (log q · (log X / log q)) = exp (log X) = X` for
`X = 4(q+2)³/27 > 0`, since `log q ≠ 0`. -/
theorem rpow_avwF {q : ℕ} (hq : 2 ≤ q) :
    ((q + 2 : ℕ) : ℝ) ^ 3 = 27 / 4 * (q : ℝ) ^ avwF q := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hlog : Real.log q ≠ 0 := (Real.log_pos hq1).ne'
  have hX : (0 : ℝ) < (4 / 27 : ℝ) * ((q + 2 : ℕ) : ℝ) ^ 3 := by positivity
  rw [Real.rpow_def_of_pos hqpos, avwF,
    show Real.log q * (Real.log ((4 / 27 : ℝ) * ((q + 2 : ℕ) : ℝ) ^ 3) / Real.log q)
      = Real.log ((4 / 27 : ℝ) * ((q + 2 : ℕ) : ℝ) ^ 3) from by field_simp,
    Real.exp_log hX]
  ring

/-- **The arithmetic heart of Theorem 7.3**: the cube of AVW's displayed lower bound is below the
quantity milestone M6 bounds, `((q+2)^{2/f(q)})³ ≤ (27/4)q²` for `q ≥ 2`.

Proof sketch: `((q+2)^{2/f})³ = ((q+2)³)^{2/f}` by the rpow power laws, and
`AlgebraicComplexity.Growth.rpow_two_div_le_of_le_mul_rpow` applied to the identity
`(q+2)³ = (27/4)·q^{f}` of `rpow_avwF` --- with `F = 27/4 ≥ 1`, `M = q ≥ 1` and `f ≥ 2` --- gives
`((q+2)³)^{2/f} ≤ (27/4)·q²`.  The step where the inequality becomes strict is
`F^{2/f} ≤ F` inside that lemma, i.e. exactly the `f ≥ 2` of `avwF_ge_two`. -/
theorem cube_rpow_two_div_avwF_le {q : ℕ} (hq : 2 ≤ q) :
    (((q + 2 : ℕ) : ℝ) ^ (2 / avwF q)) ^ 3 ≤ 27 / 4 * (q : ℝ) ^ 2 := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have ha : (0 : ℝ) ≤ ((q + 2 : ℕ) : ℝ) := by positivity
  have hroot := Growth.rpow_two_div_le_of_le_mul_rpow
    (R := ((q + 2 : ℕ) : ℝ) ^ 3) (F := 27 / 4) (M := (q : ℝ)) (f := avwF q)
    (by positivity) (by norm_num) (by linarith) (avwF_ge_two hq) (le_of_eq (rpow_avwF hq))
  have hcube : (((q + 2 : ℕ) : ℝ) ^ (2 / avwF q)) ^ (3 : ℕ)
      = (((q + 2 : ℕ) : ℝ) ^ 3) ^ (2 / avwF q) := by
    rw [← Real.rpow_natCast (((q + 2 : ℕ) : ℝ) ^ (2 / avwF q)) 3, ← Real.rpow_mul ha,
      ← Real.rpow_natCast ((q + 2 : ℕ) : ℝ) 3, ← Real.rpow_mul ha]
    ring_nf
  rw [hcube]
  exact hroot

/-- **The arithmetic heart of Remark 7.2**: `((q+2)^{2/3})³ = (q+2)² ≤ (27/4)q²` for `q ≥ 2`, i.e.
the polynomial inequality `4(q+2)² ≤ 27q²`, equivalently `23q² − 16q − 16 ≥ 0`.

[AlmanVassilevskaWilliams2018] state Remark 7.2 for `q ≥ 3`; the inequality already holds at
`q = 2` (`64 ≤ 108`) and fails only at `q = 1` (`36 > 27`). -/
theorem cube_rpow_two_thirds_le {q : ℕ} (hq : 2 ≤ q) :
    (((q + 2 : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 ≤ 27 / 4 * (q : ℝ) ^ 2 := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have ha : (0 : ℝ) ≤ ((q + 2 : ℕ) : ℝ) := by positivity
  have hcube : (((q + 2 : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = ((q + 2 : ℕ) : ℝ) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (((q + 2 : ℕ) : ℝ) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul ha,
      ← Real.rpow_natCast ((q + 2 : ℕ) : ℝ) 2]
    norm_num
  rw [hcube]
  push_cast
  nlinarith [sq_nonneg ((q : ℝ) - 2)]

end Arithmetic

section LowerBound

/-- **The interface to milestone M6**: any nonnegative `x` whose cube is at most `(27/4)q²` is a
lower bound for `Ī(CW_q^σ)`.

Proof sketch: `x³ ≤ (27/4)q² ≤ Ī(CW_q^σ)³` by `easyCW_independence_base_inequality`, and cubing is
order-reflecting on the nonnegative reals. -/
theorem le_asymptoticIndependenceNumber_gcwTable_of_cube_le (K : Type u) [CommSemiring K]
    [NoZeroDivisors K] [Nontrivial K] (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ)
    (hq : 0 < Fintype.card μ) {x : ℝ} (hx : x ^ 3 ≤ 27 / 4 * (Fintype.card μ : ℝ) ^ 2) :
    x ≤ asymptoticIndependenceNumber (gcwTable K μ σ) :=
  le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (asymptoticIndependenceNumber_nonneg _)
    (hx.trans (easyCW_independence_base_inequality K μ σ hq))

/-- **[AlmanVassilevskaWilliams2018, Theorem 7.3]**: for every `q = |μ| ≥ 2` and every permutation
`σ` of `μ`,

```text
(q+2)^{2/f(q)} ≤ Ī(CW_q^σ),      f(q) = log_q (4(q+2)³/27).
```

AVW state this for every positive integer `q`; `f(1)` is undefined, so `q ≥ 2` is assumed here (see
the module doc).

Proof sketch: `cube_rpow_two_div_avwF_le` and milestone M6, through
`le_asymptoticIndependenceNumber_gcwTable_of_cube_le`.  Note that this is *weaker* than what is
actually proved: M6 gives `((27/4)q²)^{1/3} ≤ Ī(CW_q^σ)`, and `(q+2)^{2/f(q)}` is only the largest
power of `q+2` that fits underneath it. -/
theorem avw_theorem_seven_three (K : Type u) [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
    (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ) (hq : 2 ≤ Fintype.card μ) :
    ((Fintype.card μ + 2 : ℕ) : ℝ) ^ (2 / avwF (Fintype.card μ)) ≤
      asymptoticIndependenceNumber (gcwTable K μ σ) :=
  le_asymptoticIndependenceNumber_gcwTable_of_cube_le K μ σ (by omega)
    (cube_rpow_two_div_avwF_le hq)

/-- **[AlmanVassilevskaWilliams2018, Remark 7.2], strengthened from `q ≥ 3` to `q ≥ 2`**:

```text
(q+2)^{2/3} ≤ Ī(CW_q^σ).
```

Proof sketch: `cube_rpow_two_thirds_le` (the exact rational inequality `4(q+2)² ≤ 27q²`, with no
logarithm enclosure anywhere) and milestone M6. -/
theorem avw_remark_seven_two (K : Type u) [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
    (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ) (hq : 2 ≤ Fintype.card μ) :
    ((Fintype.card μ + 2 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) ≤
      asymptoticIndependenceNumber (gcwTable K μ σ) :=
  le_asymptoticIndependenceNumber_gcwTable_of_cube_le K μ σ (by omega) (cube_rpow_two_thirds_le hq)

/-- **The sandwich for `Ī(CW_q^σ)`**, for every `q ≥ 2` and every `σ`:

```text
(q+2)^{2/f(q)} ≤ Ī(CW_q^σ) ≤ (q+2)^{1 − cornerExponent (q+2)} < q + 2.
```

The lower bound is AVW Theorem 7.3 (`avw_theorem_seven_three`, from the laser extraction of
[CoppersmithWinograd1990, §6]); the upper bound is AVW Lemma 7.1
(`asymptoticIndependenceNumber_gcwTable_le_cornerBound`, from the two corner terms of
AVW Definition 3.1 and Corollary 5.1), and it needs no hypothesis on `q` at all. -/
theorem avw_gcwTable_independence_sandwich (K : Type u) [CommSemiring K] [NoZeroDivisors K]
    [Nontrivial K] (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ)
    (hq : 2 ≤ Fintype.card μ) :
    ((Fintype.card μ + 2 : ℕ) : ℝ) ^ (2 / avwF (Fintype.card μ)) ≤
        asymptoticIndependenceNumber (gcwTable K μ σ) ∧
      asymptoticIndependenceNumber (gcwTable K μ σ) ≤ cornerBound (Fintype.card μ + 2) :=
  ⟨avw_theorem_seven_three K μ σ hq, asymptoticIndependenceNumber_gcwTable_le_cornerBound σ⟩

/-- **The numeric sandwich at `q = 6`**, on the literal index set of
[AlmanVassilevskaWilliams2018, Definition 3.1] and for every permutation `σ` of `{1,…,6}`:

```text
6.24 ≤ Ī(CW_6^σ) < 8.
```

The lower bound is the cube-root form of milestone M6, `243^{1/3} = 6.2402… ≤ Ī(CW_6^σ)`, certified
in exact rational arithmetic by `(156/25)³ = 3796416/15625 = 242.970624 ≤ 243`; it is strictly
stronger than AVW Theorem 7.3 at `q = 6`, which only gives `8^{2/f(6)} = 5.5925…`.  The upper bound
is `asymptoticIndependenceNumber_gcwTable_fin_six_lt_eight`, AVW's headline numerical claim of
Lemma 7.2 route 2.  (AVW Remark 7.3's sharper `Ī(CW_6^σ) ≥ 6.4194…` comes from the
*six*-constituent first-power analysis and is not proved here.) -/
theorem avw_gcwTable_independence_sandwich_fin_six (K : Type u) [CommSemiring K] [NoZeroDivisors K]
    [Nontrivial K] (σ : Equiv.Perm (Fin 6)) :
    (6 : ℝ) + 6 / 25 ≤ asymptoticIndependenceNumber (gcwTable K (Fin 6) σ) ∧
      asymptoticIndependenceNumber (gcwTable K (Fin 6) σ) < 8 := by
  refine ⟨le_asymptoticIndependenceNumber_gcwTable_of_cube_le K (Fin 6) σ (by simp) ?_,
    asymptoticIndependenceNumber_gcwTable_fin_six_lt_eight K σ⟩
  rw [Fintype.card_fin]
  norm_num

end LowerBound

end AlgebraicComplexity.Examples
