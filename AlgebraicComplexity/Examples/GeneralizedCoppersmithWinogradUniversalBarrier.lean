/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinogradBarrier
import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinogradSliceRankUpper
import AlgebraicComplexity.MatrixMultiplication.UniversalSliceRankBarrier

/-!
# The universal-method barrier for the generalized Coppersmith--Winograd tensors

This file proves the `CW` instance of [Alman2019, Theorem 5.7]: **no generalized
Coppersmith--Winograd tensor can prove a bound below `13/6 = 2.1666…` on `ω` by the Universal
method**, uniformly in the parameter `q ≥ 1` and the middle permutation `σ`.

```text
ω_u(CW_{q,σ}) ≥ 2 / s = 13/6      for every q ≥ 1 and every σ,
```

assuming the existence of at least one universal certificate for the tensor. Monotonicity of slice
rank under polynomial degeneration (thesis Proposition 5.1) is now proved by
`Tensor.sliceRankDegenerationMonotone_holds`; the older theorem signatures accepting the packaged
proposition `Tensor.SliceRankDegenerationMonotone` remain as compatibility wrappers, followed by
unconditional primed forms.

## The two inputs

* `R̃(CW_q^σ) ≥ q + 2` --- conciseness, `card_le_asymptoticRank_gcwTable`; combined with
  `asymptoticRank_pow_le_of_isCoordinateConcise` this gives the geometric lower bound
  `(q+2)^n ≤ R̃(CW^{⊗n})` that Theorem 5.1 consumes.
* `S̃(CW_q^σ) ≤ (q+2)^{12/13}` --- the block-entropy bound
  `asymptoticSliceRank_gcwTable_le_rpow_mul` at the rational parameter `u = 3/(q+4)`, followed by
  the elementary inequality `gcw_rpow_mul_le_rpow` proved below.

Corollary 5.2 then gives `ω_u ≥ 2/(12/13) = 13/6`.

## The exponent `12/13`, and the distance to the thesis' `2.16805`

Alman's constant is `2.16805…`, and it is exactly the `q = 1` value: there
`S̃(CW_{1,σ}) = 2.7551046…` (the parameter `u` being the positive root of `4u² + u − 2 = 0`) and
`R̃ = 3`, so the sharp exponent is `s₁ = log 2.7551046 / log 3 = 0.9224869…` and
`2/s₁ = 2.1680525…`.  Two deliberate approximations separate `13/6` from that number:

* **the rational parameter family.**  Instead of the optimal `u_q = (√(q²+32) − q)/8` (the root of
  `4u² + qu − 2 = 0`) this file uses `u_q = 3/(q+4)`, which is exact at `q = 2` and costs `4·10⁻⁵`
  in relative terms at `q = 1`.  It has the decisive advantage that the resulting bound is a
  *rational function of `q`*, namely

  ```text
  (u_q^{1/3}(q + u_q + 1/u_q))³ = (2q+5)^6 / (9(q+4)^4),
  ```

  so the whole optimization over `q` collapses to one polynomial inequality.  It caps the
  attainable constant at `2.1679680…`, the `q = 1` value of the family.
* **the small-denominator exponent.**  Certifying `S̃ ≤ (q+2)^{a/b}` amounts to the integer
  inequality `((2q+5)^6)^b ≤ 9^b (q+4)^{4b} (q+2)^{3a}`, whose numbers grow with `b`; the smallest
  admissible exponent for the family is `0.9225228…`, and `12/13 = 0.9230769…` is *the* simplest
  rational above it --- no fraction with `b ≤ 141` lies in between, and the next improvement is
  `131/142`, worth `2.1679389…`.  Reaching `2.16805` itself would need the sharper `u` *and* the
  exponent `1083/1174`, i.e. exact arithmetic on numbers with thousands of digits; the honest route
  to it is certified *logarithms* of the kind in `Analysis/LogConstants.lean`, at eight-digit
  precision, rather than a rational power certificate.  That is done: see the eight-digit section below.

So the barrier proved here is `13/6 = 2.1666…` where the thesis states `2.16805…`, a relative loss
of `6·10⁻⁴`, with everything else identical.

## The polynomial inequality

`gcw_pow_le` is `((2q+5)^6/(9(q+4)^4))^{13} ≤ (q+2)^{36}` for all `q ≥ 1`.  For `q ≤ 8` it is eight
explicit rational comparisons; for `q ≥ 9` it follows from `(2q+5)² ≤ 4(q+2)(q+4)` (an inequality
with slack `4q+7`) together with the single integer check `64^{13} ≤ 9^{13}·13^{10}`, which is what
makes the tail uniform in `q`.

## Position in the library

Layer 4 (`AlgebraicComplexity/Examples/`), a named client: the `CW` instantiation of
`MatrixMultiplication/UniversalSliceRankBarrier.lean`.
-/

namespace AlgebraicComplexity.Analysis

/-! ### The two block-entropy certificate values

The generalized Coppersmith--Winograd block-entropy bound `S̃(CW_q^σ) ≤ u^{1/3}(q + u + 1/u)` is
rational as soon as `u` is a rational *cube*.  At `q = 1` the choice `u = (21/25)³` gives

```text
S̃(CW_1^σ) ≤ (21/25)(1 + (21/25)³ + (25/21)³) = 474609871/172265625 = 2.7551049…,
```

within `4·10⁻⁸` of the true optimum `2.75510464…`; at `q = 5` the choice `u = (13/19)³` gives
`127218805/22024249 = 5.7763061…`, within `4·10⁻⁶` of `5.77628514…`.

Both logarithms are certified by *anchoring*: each value is a smooth rational times a factor
within `10⁻³` of `1`, and only the latter needs the series.  The anchors are

```text
474609871/172265625 = (135/49) · (474609871/474609375),
127218805/22024249  = (81/14)  / (1783964169/1781063270),
```

so the series points are `248/474609623 ≈ 5.2·10⁻⁷` and `2900899/3565027439 ≈ 8.1·10⁻⁴`, at which
*one* term already beats `10⁻⁹`.

The two rationals are thesis optimizer choices, not canonical constants, so these enclosures live
with their client rather than in `Analysis/LogConstants.lean` (see that file's module doc); they
keep the `AlgebraicComplexity.Analysis` namespace because their statements are pure analysis and
the established names are stable.  Only the machinery they call — `le_log_of_logRatioLower`,
`log_le_of_logRatioUpper`, and the `log 2`/`log 3`/`log 5`/`log 7` enclosures — is layer-2.
-/

/-- Certified rational lower bound `log (474609871/474609375) ≥ 1.0450694127·10⁻⁶`, from the atanh
series at `x = 248/474609623` with a single term.  The true value is `1.04506941276250765·10⁻⁶`. -/
theorem log_gcwOneAnchorRatio_ge_sharp :
    (10450694127 : ℝ) / 10000000000000000 ≤ Real.log (474609871 / 474609375) :=
  le_log_of_logRatioLower (x := (248 / 474609623 : ℝ)) (by norm_num) (by norm_num) 1 (by norm_num)
    (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

/-- Certified rational upper bound `log (474609871/474609375) ≤ 1.0450694128·10⁻⁶`, from the same
one-term series with its geometric remainder. -/
theorem log_gcwOneAnchorRatio_le_sharp :
    Real.log (474609871 / 474609375) ≤ 10450694128 / 10000000000000000 :=
  log_le_of_logRatioUpper (x := (248 / 474609623 : ℝ)) (by norm_num) (by norm_num) 1 (by norm_num)
    (by norm_num [logRatioUpper, atanhPartial, atanhRemainder, Finset.sum_range_succ])

/-- The anchor identity `474609871/172265625 = (3³·5/7²)·(474609871/474609375)`, in logarithmic
form. -/
theorem log_gcwOneCertificate_eq :
    Real.log (474609871 / 172265625) =
      3 * Real.log 3 + Real.log 5 - 2 * Real.log 7 + Real.log (474609871 / 474609375) := by
  rw [show (474609871 : ℝ) / 172265625 = (3 ^ 3 * 5 / 7 ^ 2) * (474609871 / 474609375) by
      norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- **Certified rational upper bound `log (474609871/172265625) ≤ 1.0134555265`.**  The true value
is `1.01345552539721560…`.  This is the denominator of the thesis constant
`2 log 3 / log S̃(CW_1^σ) = 2.16805…`. -/
theorem log_gcwOneCertificate_le_sharp :
    Real.log (474609871 / 172265625) ≤ 10134555265 / 10000000000 := by
  rw [log_gcwOneCertificate_eq]
  linarith [log_three_le_sharp, log_five_le_sharp, log_seven_ge_sharp,
    log_gcwOneAnchorRatio_le_sharp]

/-- Certified rational lower bound `log (474609871/172265625) ≥ 1.0134555247`; together with
`log_gcwOneCertificate_le_sharp` this pins the value to within `1.8·10⁻⁹`. -/
theorem log_gcwOneCertificate_ge_sharp :
    (10134555247 : ℝ) / 10000000000 ≤ Real.log (474609871 / 172265625) := by
  rw [log_gcwOneCertificate_eq]
  linarith [log_three_ge_sharp, log_five_ge_sharp, log_seven_le_sharp,
    log_gcwOneAnchorRatio_ge_sharp]

/-- Certified rational lower bound `log (1783964169/1781063270) ≥ 1.627420293·10⁻³`, from the atanh
series at `x = 2900899/3565027439` with a single term.  The true value is `1.62742065237·10⁻³`. -/
theorem log_gcwFiveAnchorRatio_ge_sharp :
    (1627420293 : ℝ) / 1000000000000 ≤ Real.log (1783964169 / 1781063270) :=
  le_log_of_logRatioLower (x := (2900899 / 3565027439 : ℝ)) (by norm_num) (by norm_num) 1
    (by norm_num) (by norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ])

/-- The anchor identity `127218805/22024249 = (3⁴/(2·7))/(1783964169/1781063270)`, in logarithmic
form. -/
theorem log_gcwFiveCertificate_eq :
    Real.log (127218805 / 22024249) =
      4 * Real.log 3 - Real.log 2 - Real.log 7 - Real.log (1783964169 / 1781063270) := by
  rw [show (127218805 : ℝ) / 22024249 = (3 ^ 4 / (2 * 7)) / (1783964169 / 1781063270) by
      norm_num, Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  push_cast
  ring

/-- **Certified rational upper bound `log (127218805/22024249) ≤ 1.7537644057`.**  The true value
is `1.75376440440480740…`.  This is the denominator of the `q = 5` entry
`2 log 7 / log S̃(CW_5^σ) = 2.21912…` of the thesis table. -/
theorem log_gcwFiveCertificate_le_sharp :
    Real.log (127218805 / 22024249) ≤ 17537644057 / 10000000000 := by
  rw [log_gcwFiveCertificate_eq]
  linarith [log_three_le_sharp, log_two_ge_sharp, log_seven_ge_sharp,
    log_gcwFiveAnchorRatio_ge_sharp]

end AlgebraicComplexity.Analysis

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The elementary inequality behind the exponent `12/13` -/

section Numeric

/-- If `X^b ≤ Y^a` for natural exponents with `b ≠ 0`, then `X ≤ Y^{a/b}` as a real power.  This is
the bridge from a rational certificate to an `rpow` bound. -/
private theorem le_rpow_div_of_pow_le {X Y : ℝ} {a b : ℕ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hb : 0 < b)
    (h : X ^ b ≤ Y ^ a) : X ≤ Y ^ ((a : ℝ) / b) := by
  calc X = (X ^ b) ^ ((b : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX hb.ne').symm
    _ ≤ (Y ^ a) ^ ((b : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = Y ^ ((a : ℝ) / b) := by
        rw [← Real.rpow_natCast Y a, ← Real.rpow_mul hY, div_eq_mul_inv]

/-- **The tail estimate, in atoms.**  With `A = 2q+5`, `B = q+2` and `C = q+4`, the hypotheses
`A² ≤ 4BC`, `B ≤ C` and `13 ≤ C` give `(A^6)^{13} ≤ B^{36}(9C^4)^{13}`.

Stating it for three unconstrained reals is not generality for its own sake: it keeps `ring` from
ever expanding a degree-78 polynomial in `q`, which is the difference between a proof that
elaborates in seconds and one that does not elaborate at all.

Proof sketch: `(A^6)^{13} = (A²)^{39} ≤ (4BC)^{39} = (4^{39}B³)·(B^{36}C^{39})`, and
`4^{39} B³ = 64^{13} B³ ≤ (9^{13}·13^{10})·B³ ≤ 9^{13}C^{10}·C³ = 9^{13}C^{13}`, the first step
being the integer check `64^{13} ≤ 9^{13}·13^{10}` --- the only numerical input of the tail. -/
private theorem gcw_tail_pow_le {A B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hbase : A ^ 2 ≤ 4 * (B * C)) (hBC : B ≤ C) (h13 : 13 ≤ C) :
    (A ^ 6) ^ 13 ≤ B ^ 36 * (9 * C ^ 4) ^ 13 := by
  have hnum : (4 : ℝ) ^ 39 ≤ 9 ^ 13 * 13 ^ 10 := by norm_num
  have hkey : (4 : ℝ) ^ 39 * B ^ 3 ≤ 9 ^ 13 * C ^ 13 :=
    calc (4 : ℝ) ^ 39 * B ^ 3 ≤ (9 ^ 13 * 13 ^ 10) * B ^ 3 :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ ≤ (9 ^ 13 * C ^ 10) * C ^ 3 := by
          have h1 : (13 : ℝ) ^ 10 ≤ C ^ 10 := pow_le_pow_left₀ (by norm_num) h13 10
          have h2 : B ^ 3 ≤ C ^ 3 := pow_le_pow_left₀ hB.le hBC 3
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (by positivity)
            (by positivity)
      _ = 9 ^ 13 * C ^ 13 := by ring
  calc (A ^ 6) ^ 13 = (A ^ 2) ^ 39 := by ring
    _ ≤ (4 * (B * C)) ^ 39 := pow_le_pow_left₀ (by positivity) hbase 39
    _ = ((4 : ℝ) ^ 39 * B ^ 3) * (B ^ 36 * C ^ 39) := by ring
    _ ≤ ((9 : ℝ) ^ 13 * C ^ 13) * (B ^ 36 * C ^ 39) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = B ^ 36 * (9 * C ^ 4) ^ 13 := by ring

/-- **The polynomial inequality behind the barrier**: for every `q ≥ 1`,

```text
((2q+5)^6 / (9(q+4)^4))^{13} ≤ (q+2)^{36}.
```

The left-hand side is the cube of the block-entropy bound `u^{1/3}(q+u+1/u)` at `u = 3/(q+4)`, so
this says exactly `S̃(CW_q^σ) ≤ (q+2)^{12/13}` after taking `39`-th roots.

Proof sketch: for `q ≤ 8`, eight explicit rational comparisons.  For `q ≥ 9`, from
`(2q+5)² ≤ 4(q+2)(q+4)` one gets `(2q+5)^{78} ≤ 4^{39}(q+2)^{39}(q+4)^{39}`, and since `4^{39} =
64^{13}` the claim reduces to `64^{13}(q+2)³ ≤ 9^{13}(q+4)^{13}`, which follows from
`(q+4)^{10} ≥ 13^{10}` and the integer check `64^{13} ≤ 9^{13}·13^{10}`. -/
theorem gcw_pow_le (q : ℕ) (hq : 1 ≤ q) :
    (((2 * (q : ℝ) + 5) ^ 6 / (9 * ((q : ℝ) + 4) ^ 4)) ^ 13 : ℝ) ≤ ((q : ℝ) + 2) ^ 36 := by
  have hden : (0 : ℝ) < (9 * ((q : ℝ) + 4) ^ 4) ^ 13 := by positivity
  rw [div_pow, div_le_iff₀ hden]
  rcases Nat.lt_or_ge q 9 with hlt | hgt
  · have hle : q ≤ 8 := by omega
    interval_cases q <;> norm_num
  · have hx : (9 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hgt
    have hbase : (2 * (q : ℝ) + 5) ^ 2 ≤ 4 * (((q : ℝ) + 2) * ((q : ℝ) + 4)) := by nlinarith
    exact gcw_tail_pow_le (by linarith) (by linarith) hbase (by linarith) (by linarith)

/-- **The closed-form block-entropy bound at `u = 3/(q+4)` is below `(q+2)^{12/13}`**, for every
`q ≥ 1`:

```text
u^{1/3} · (q + u + 1/u) ≤ (q+2)^{12/13}      with u = 3/(q+4).
```

Proof sketch: both sides are nonnegative, so it suffices to compare cubes.  The left cube is the
rational function `(2q+5)^6/(9(q+4)^4)` (because `q + u + 1/u = (2q+5)²/(3(q+4))`), the right cube
is `(q+2)^{36/13}`, and `gcw_pow_le` is exactly the `13`-th power form of that comparison. -/
theorem gcw_rpow_mul_le_rpow (q : ℕ) (hq : 1 ≤ q) :
    ((3 : ℝ) / ((q : ℝ) + 4)) ^ ((3 : ℝ)⁻¹) *
        ((q : ℝ) + (3 : ℝ) / ((q : ℝ) + 4) + ((3 : ℝ) / ((q : ℝ) + 4))⁻¹) ≤
      ((q : ℝ) + 2) ^ ((12 : ℝ) / 13) := by
  have hq4 : (0 : ℝ) < (q : ℝ) + 4 := by positivity
  set u : ℝ := (3 : ℝ) / ((q : ℝ) + 4) with hudef
  have hu : 0 < u := by rw [hudef]; positivity
  set s : ℝ := (q : ℝ) + u + u⁻¹ with hsdef
  have hs : 0 < s := by rw [hsdef]; positivity
  have hcube : (u ^ ((3 : ℝ)⁻¹) * s) ^ 3 = u * s ^ 3 := by
    rw [mul_pow, ← Real.rpow_natCast (u ^ ((3 : ℝ)⁻¹)) 3, ← Real.rpow_mul hu.le]
    norm_num
  have hrat : u * s ^ 3 = (2 * (q : ℝ) + 5) ^ 6 / (9 * ((q : ℝ) + 4) ^ 4) := by
    rw [hsdef, hudef]
    field_simp
    ring
  have hleft : (u ^ ((3 : ℝ)⁻¹) * s) ^ 3 ≤ ((q : ℝ) + 2) ^ ((36 : ℝ) / 13) := by
    rw [hcube, hrat]
    exact le_rpow_div_of_pow_le (by positivity) (by positivity) (by norm_num) (gcw_pow_le q hq)
  have hright : (((q : ℝ) + 2) ^ ((12 : ℝ) / 13)) ^ 3 = ((q : ℝ) + 2) ^ ((36 : ℝ) / 13) := by
    rw [← Real.rpow_natCast (((q : ℝ) + 2) ^ ((12 : ℝ) / 13)) 3,
      ← Real.rpow_mul (by positivity)]
    norm_num
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
  rw [hright]
  exact hleft

end Numeric

/-! ## The barrier -/

section Barrier

variable {K : Type u} [Field K] {μ : Type} [Fintype μ] [DecidableEq μ]

/-- **`S̃(CW_q^σ) ≤ (q+2)^{12/13}`** for every `q ≥ 1` and every `σ`: the block-entropy bound of
`asymptoticSliceRank_gcwTable_le_rpow_mul` at the rational parameter `u = 3/(q+4)`, estimated by
`gcw_rpow_mul_le_rpow`.

The exponent `12/13 = 0.923…` is above the sharp `log_3 2.75510… = 0.92249…` of [Alman2019]; see
the module documentation for the two sources of the gap. -/
theorem asymptoticSliceRank_gcwTable_le_rpow (σ : Equiv.Perm μ) (hq : 1 ≤ Fintype.card μ) :
    Tensor.asymptoticSliceRank (coordinateTensor (gcwTable K μ σ)) ≤
      ((Fintype.card μ : ℝ) + 2) ^ ((12 : ℝ) / 13) := by
  have hq4 : (0 : ℝ) < (Fintype.card μ : ℝ) + 4 := by positivity
  refine le_trans (asymptoticSliceRank_gcwTable_le_rpow_mul (K := K) σ hq
    (u := (3 : ℝ) / ((Fintype.card μ : ℝ) + 4)) (by positivity)) ?_
  exact gcw_rpow_mul_le_rpow (Fintype.card μ) hq

/-- **[Alman2019, Theorem 5.7], with the certified constant `13/6 = 2.1666…`** in place of the
thesis' `2.16805…`.  For every field `K`, every parameter `q ≥ 1`, and every middle permutation
`σ`, the Universal method applied to the generalized Coppersmith--Winograd tensor `CW_q^σ` cannot
prove any bound on `ω` below `13/6`:

```text
ω_u(CW_{q,σ}) ≥ 13/6 = 2.1666…
```

The compatibility form retains two hypotheses beyond the tensor itself:

* `hobl`, the packaged statement `Tensor.SliceRankDegenerationMonotone` (thesis Proposition 5.1).
  It is no longer an open input: `Tensor.sliceRankDegenerationMonotone_holds` constructs it over
  every field. The primed theorem below supplies that proof automatically.
* `hne`, the existence of at least one universal certificate for `CW_q^σ`.  This is *necessary*:
  `universalExponent` is an infimum, and Lean's `sInf ∅ = 0`, so without a certificate the
  statement is false as stated (and vacuous as mathematics --- the Universal method proves nothing
  at all about such a tensor).

Proof sketch: Corollary 5.2 (`two_div_le_universalExponent_of_asymptoticSliceRank`) with
`R = q+2 ≤ R̃(CW_q^σ)` (conciseness, `card_le_asymptoticRank_gcwTable`, powered up by
`asymptoticRank_pow_le_of_isCoordinateConcise`), `S = (q+2)^{12/13}` and `s = 12/13`, using
`asymptoticSliceRank_gcwTable_le_rpow`. -/
theorem thirteen_div_six_le_universalExponent_gcwTable (σ : Equiv.Perm μ)
    (hq : 1 ≤ Fintype.card μ)
    (hobl : Tensor.SliceRankDegenerationMonotone.{u, u, u} K)
    (hne : (universalValues K (coordinateTensor (gcwTable K μ σ))).Nonempty) :
    (13 : ℝ) / 6 ≤ universalExponent K (coordinateTensor (gcwTable K μ σ)) := by
  have hqR : (1 : ℝ) ≤ (Fintype.card μ : ℝ) := by exact_mod_cast hq
  have hconc : ∀ i, Tensor.IsCoordinateConcise (gcwTable K μ σ) i :=
    fun i ↦ isCoordinateConcise_gcwTable K σ i
  have hR : (0 : ℝ) < (Fintype.card μ : ℝ) + 2 := by linarith
  have hS : (1 : ℝ) < ((Fintype.card μ : ℝ) + 2) ^ ((12 : ℝ) / 13) := by
    refine Real.one_lt_rpow_iff_of_pos hR |>.mpr ?_
    exact Or.inl ⟨by linarith, by norm_num⟩
  have hRle : ∀ n : ℕ, 1 ≤ n →
      ((Fintype.card μ : ℝ) + 2) ^ n ≤
        Tensor.asymptoticRank (Tensor.power (coordinateTensor (gcwTable K μ σ)) n) := by
    intro n _
    calc ((Fintype.card μ : ℝ) + 2) ^ n
        ≤ Tensor.asymptoticRank (coordinateTensor (gcwTable K μ σ)) ^ n :=
          pow_le_pow_left₀ (by linarith) (card_le_asymptoticRank_gcwTable (K := K) σ) n
      _ ≤ Tensor.asymptoticRank (Tensor.power (coordinateTensor (gcwTable K μ σ)) n) :=
          asymptoticRank_pow_le_of_isCoordinateConcise K hconc n
  have hmain := two_div_le_universalExponent_of_asymptoticSliceRank K hobl (T :=
      coordinateTensor (gcwTable K μ σ)) (R := (Fintype.card μ : ℝ) + 2)
    (S := ((Fintype.card μ : ℝ) + 2) ^ ((12 : ℝ) / 13)) (s := (12 : ℝ) / 13)
    hne hR hS (by norm_num) le_rfl hRle (asymptoticSliceRank_gcwTable_le_rpow σ hq)
  rwa [show (2 : ℝ) / ((12 : ℝ) / 13) = 13 / 6 by norm_num] at hmain

/-- **The Universal method cannot prove `ω = 2` through any generalized Coppersmith--Winograd
tensor**, with the explicit margin `1/6`. This backward-compatible form accepts the packaged
slice-rank theorem explicitly; the primed theorem below discharges it automatically. -/
theorem two_lt_universalExponent_gcwTable (σ : Equiv.Perm μ) (hq : 1 ≤ Fintype.card μ)
    (hobl : Tensor.SliceRankDegenerationMonotone.{u, u, u} K)
    (hne : (universalValues K (coordinateTensor (gcwTable K μ σ))).Nonempty) :
    2 < universalExponent K (coordinateTensor (gcwTable K μ σ)) :=
  lt_of_lt_of_le (by norm_num)
    (thirteen_div_six_le_universalExponent_gcwTable σ hq hobl hne)

end Barrier
section Unconditional

/-! ### Unconditional forms

`Tensor.sliceRankDegenerationMonotone_holds` discharges the obligation, so Theorem 5.7 of
[Alman2019] holds outright: no universal-method analysis of any generalized Coppersmith--Winograd
tensor, over any field, can prove `ω < 13/6`. -/

variable {K : Type u} [Field K]

/-- Theorem 5.7 of [Alman2019], unconditionally: `13/6 ≤ ω_u(CW_q^σ)` for every `q ≥ 1`, `σ`. -/
theorem thirteen_div_six_le_universalExponent_gcwTable' {μ : Type} [Fintype μ] [DecidableEq μ]
    (σ : Equiv.Perm μ) (hq : 1 ≤ Fintype.card μ)
    (hne : (universalValues K (Tensor.coordinateTensor (gcwTable K μ σ))).Nonempty) :
    (13 : ℝ) / 6 ≤ universalExponent K (Tensor.coordinateTensor (gcwTable K μ σ)) :=
  thirteen_div_six_le_universalExponent_gcwTable σ hq
    (Tensor.sliceRankDegenerationMonotone_holds K) hne

/-- The qualitative form: the universal method cannot reach `ω = 2` on any `CW_q^σ`. -/
theorem two_lt_universalExponent_gcwTable' {μ : Type} [Fintype μ] [DecidableEq μ]
    (σ : Equiv.Perm μ) (hq : 1 ≤ Fintype.card μ)
    (hne : (universalValues K (Tensor.coordinateTensor (gcwTable K μ σ))).Nonempty) :
    (2 : ℝ) < universalExponent K (Tensor.coordinateTensor (gcwTable K μ σ)) :=
  lt_of_lt_of_le (by norm_num) (thirteen_div_six_le_universalExponent_gcwTable' σ hq hne)

end Unconditional

section Sharp

/-! ## The sharp form: the thesis constant `2.16805…`

The `13/6` barrier above trades two approximations for a single small-denominator rational power
certificate.  This section pays for the exact constant of [Alman2019, Theorem 5.7] instead, using
the eight-digit logarithm enclosures of `Analysis/LogConstants.lean`, and supersedes the remark in
the module documentation that the sharp constant is future work.

Three statements land:

```text
2.168      ≤ ω_u(CW_q^σ)      for every q ≥ 1 and every σ   (avw_thesis_constant_…)
2.16805229 ≤ ω_u(CW_1^σ)      the thesis constant 2.1680525…
2.21912378 ≤ ω_u(CW_5^σ)      the thesis table entry 2.21912…
```

### Where the two extra digits come from

Both the `q = 1` and the `q = 5` numbers use a *cube* rational parameter, for which the
block-entropy bound `S̃(CW_q^σ) ≤ u^{1/3}(q + u + 1/u)` is itself rational:

```text
u = (21/25)³  ⟹  S̃(CW_1^σ) ≤ 474609871/172265625 = 2.7551049…   (optimum 2.75510464…)
u = (13/19)³  ⟹  S̃(CW_5^σ) ≤ 127218805/22024249  = 5.7763061…   (optimum 5.77628514…)
```

`Analysis/LogConstants.lean` certifies `log` of both to nine digits by anchoring
(`log_gcwOneCertificate_le_sharp`, `log_gcwFiveCertificate_le_sharp`), and Theorem 5.1 in its
printed form `ω_u ≥ 2 log R̃ / log S̃` then gives the two named values directly, with `R̃ ≥ q + 2`
as before.  The `q = 1` margin is `2.1·10⁻⁹`: the enclosures support `2.16805229` and no more.

### The uniform `2.168`

For the all-`q` statement the exponent `12/13 = 0.9230769…` of `gcw_pow_le` is not enough --- it
yields `2.1666…` --- and the sharp exponent needed is `1000/1084 = 0.92250922…`, whose rational
power certificate `S̃^{1084} ≤ (q+2)^{1000}` involves numbers with thousands of digits.  The route
taken here is logarithmic instead, and splits at `q = 2`:

* `q = 1` uses the cube parameter `u = (21/25)³` above, i.e. `gcwOneCertificate_le_rpow`; the
  rational family `u = 3/(q+4)` would cap at `2.1679680…`, just *below* `2.168`, so the sharper
  parameter is genuinely needed at the one binding value of `q`.
* `q ≥ 2` uses the rational family, where the slack is `4·10⁻³` rather than `2·10⁻⁵`: in
  logarithmic form the claim is

  ```text
  6 log(2q+5) ≤ 2 log 3 + 4 log(q+4) + (3000/1084) log(q+2)      (gcw_sharp_log_bound)
  ```

  proved by induction from `q = 2` (where it is `6 log 3 ≤ (4 + 6000/1084) log 2`, closed by the
  six-digit enclosures) with the increment step `gcw_sharp_log_step`.  The step compares one upper
  and two lower bounds on logarithmic increments from `Analysis/LogConstants.lean` ---
  `log_sub_log_le_sq_div` and `two_div_le_log_succ_sub_log` --- and reduces to

  ```text
  (24q+72)/((2q+7)(2q+5)) ≤ 8/(2q+9) + (3000/1084)·2/(2q+5),
  ```

  i.e. to `1664q² + 2472q - 5228 ≥ 0`, which holds for `q ≥ 2` with room to spare.

Every statement in this section is unconditional: the obligation
`Tensor.SliceRankDegenerationMonotone` is discharged by `Tensor.sliceRankDegenerationMonotone_holds`
exactly as in the `Unconditional` section above.  The hypothesis `hne` --- that `CW_q^σ` has at
least one universal certificate --- remains, for the same reason as there.
-/

section SharpNumeric

open AlgebraicComplexity.Analysis

/-- **The increment step of the sharp `q ≥ 2` bound.**  For every real `x ≥ 2`,

```text
6(log(2x+7) - log(2x+5)) ≤ 4(log(x+5) - log(x+4)) + (3000/1084)(log(x+3) - log(x+2)).
```

The left increment is bounded above by `log_sub_log_le_sq_div`, giving
`(24x+72)/((2x+7)(2x+5))`, and the two right increments below by `two_div_le_log_succ_sub_log`,
giving `4·2/(2x+9)` and `(3000/1084)·2/(2x+5)`.  What remains is the rational inequality whose
numerator, over the common denominator `271(2x+9)(2x+7)(2x+5)`, is `1664x² + 2472x - 5228`. -/
theorem gcw_sharp_log_step {x : ℝ} (hx : (2 : ℝ) ≤ x) :
    6 * (Real.log (2 * x + 7) - Real.log (2 * x + 5)) ≤
      4 * (Real.log (x + 5) - Real.log (x + 4)) +
        (3000 / 1084 : ℝ) * (Real.log (x + 3) - Real.log (x + 2)) := by
  have h5 : (0 : ℝ) < 2 * x + 5 := by linarith
  have hA : 6 * (Real.log (2 * x + 7) - Real.log (2 * x + 5)) ≤
      (24 * x + 72) / ((2 * x + 7) * (2 * x + 5)) := by
    have h := log_sub_log_le_sq_div h5 (by linarith : 2 * x + 5 ≤ 2 * x + 7)
    calc 6 * (Real.log (2 * x + 7) - Real.log (2 * x + 5))
        ≤ 6 * (((2 * x + 7) ^ 2 - (2 * x + 5) ^ 2) / (2 * (2 * x + 7) * (2 * x + 5))) := by
          linarith
      _ = (24 * x + 72) / ((2 * x + 7) * (2 * x + 5)) := by
          field_simp
          ring
  have hB : 4 * (2 / (2 * x + 9)) ≤ 4 * (Real.log (x + 5) - Real.log (x + 4)) := by
    have h := two_div_le_log_succ_sub_log (x := x + 4) (by linarith)
    have e1 : x + 4 + 1 = x + 5 := by ring
    have e2 : 2 * (x + 4) + 1 = 2 * x + 9 := by ring
    rw [e1, e2] at h
    linarith
  have hC : (3000 / 1084 : ℝ) * (2 / (2 * x + 5)) ≤
      (3000 / 1084 : ℝ) * (Real.log (x + 3) - Real.log (x + 2)) := by
    have h := two_div_le_log_succ_sub_log (x := x + 2) (by linarith)
    have e1 : x + 2 + 1 = x + 3 := by ring
    have e2 : 2 * (x + 2) + 1 = 2 * x + 5 := by ring
    rw [e1, e2] at h
    linarith
  have key : (24 * x + 72) / ((2 * x + 7) * (2 * x + 5)) ≤
      4 * (2 / (2 * x + 9)) + (3000 / 1084 : ℝ) * (2 / (2 * x + 5)) := by
    rw [← sub_nonneg]
    have hid : 4 * (2 / (2 * x + 9)) + (3000 / 1084 : ℝ) * (2 / (2 * x + 5)) -
        (24 * x + 72) / ((2 * x + 7) * (2 * x + 5)) =
        (1664 * x ^ 2 + 2472 * x - 5228) /
          (271 * ((2 * x + 9) * ((2 * x + 7) * (2 * x + 5)))) := by
      field_simp
      ring
    rw [hid]
    refine div_nonneg ?_ (by positivity)
    nlinarith [sq_nonneg (x - 2)]
  linarith

/-- **The block-entropy bound of the rational family, in logarithmic form, at the sharp exponent
`1000/1084`.**  For every natural `q ≥ 2`,

```text
6 log(2q+5) ≤ 2 log 3 + 4 log(q+4) + (3000/1084) log(q+2),
```

which is `(2q+5)^6/(9(q+4)^4) ≤ (q+2)^{3000/1084}`, i.e. the cube of
`S̃(CW_q^σ) ≤ (q+2)^{1000/1084}` at the parameter `u = 3/(q+4)`.

`Nat.le_induction` from the base case `q = 2`, where the statement collapses to
`6 log 3 ≤ (4 + 6000/1084) log 2` (`6.5917 ≤ 6.6092`, closed by the six-digit `log_three_le` and
`log_two_ge`), with `gcw_sharp_log_step` as the increment. -/
theorem gcw_sharp_log_bound (q : ℕ) (hq : 2 ≤ q) :
    6 * Real.log (2 * (q : ℝ) + 5) ≤
      2 * Real.log 3 + 4 * Real.log ((q : ℝ) + 4) +
        (3000 / 1084 : ℝ) * Real.log ((q : ℝ) + 2) := by
  induction q, hq using Nat.le_induction with
  | base =>
      have h9 : Real.log 9 = 2 * Real.log 3 := by
        rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
        push_cast
        ring
      have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
        push_cast
        ring
      have e1 : 2 * ((2 : ℕ) : ℝ) + 5 = 9 := by norm_num
      have e2 : ((2 : ℕ) : ℝ) + 4 = 6 := by norm_num
      have e3 : ((2 : ℕ) : ℝ) + 2 = 4 := by norm_num
      rw [e1, e2, e3, h9, h6, h4]
      linarith [log_three_le, log_two_ge]
  | succ n hn ih =>
      have hx : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h := gcw_sharp_log_step hx
      have e1 : 2 * ((n : ℝ) + 1) + 5 = 2 * (n : ℝ) + 7 := by ring
      have e2 : (n : ℝ) + 1 + 4 = (n : ℝ) + 5 := by ring
      have e3 : (n : ℝ) + 1 + 2 = (n : ℝ) + 3 := by ring
      push_cast
      rw [e1, e2, e3]
      linarith

/-- **The closed-form block-entropy bound at `u = 3/(q+4)` is below `(q+2)^{1000/1084}`**, for
every `q ≥ 2`.  The sharp-exponent counterpart of `gcw_rpow_mul_le_rpow`, and the reason the split
at `q = 2` is affordable: away from `q = 1` the rational family has four digits of slack.

Proof sketch: both sides are nonnegative, so it suffices to compare cubes; the left cube is
`(2q+5)^6/(9(q+4)^4)` and the comparison of its logarithm with `(3000/1084) log(q+2)` is
`gcw_sharp_log_bound`. -/
theorem gcw_sharp_rpow_mul_le_rpow (q : ℕ) (hq : 2 ≤ q) :
    ((3 : ℝ) / ((q : ℝ) + 4)) ^ ((3 : ℝ)⁻¹) *
        ((q : ℝ) + (3 : ℝ) / ((q : ℝ) + 4) + ((3 : ℝ) / ((q : ℝ) + 4))⁻¹) ≤
      ((q : ℝ) + 2) ^ ((1000 : ℝ) / 1084) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq4 : (0 : ℝ) < (q : ℝ) + 4 := by linarith
  set u : ℝ := (3 : ℝ) / ((q : ℝ) + 4) with hudef
  have hu : 0 < u := by rw [hudef]; positivity
  set s : ℝ := (q : ℝ) + u + u⁻¹ with hsdef
  have hs : 0 < s := by rw [hsdef]; positivity
  have hcube : (u ^ ((3 : ℝ)⁻¹) * s) ^ 3 = u * s ^ 3 := by
    rw [mul_pow, ← Real.rpow_natCast (u ^ ((3 : ℝ)⁻¹)) 3, ← Real.rpow_mul hu.le]
    norm_num
  have hrat : u * s ^ 3 = (2 * (q : ℝ) + 5) ^ 6 / (9 * ((q : ℝ) + 4) ^ 4) := by
    rw [hsdef, hudef]
    field_simp
    ring
  have hV : (0 : ℝ) < (2 * (q : ℝ) + 5) ^ 6 / (9 * ((q : ℝ) + 4) ^ 4) := by positivity
  have hlogV : Real.log ((2 * (q : ℝ) + 5) ^ 6 / (9 * ((q : ℝ) + 4) ^ 4)) =
      6 * Real.log (2 * (q : ℝ) + 5) - 2 * Real.log 3 - 4 * Real.log ((q : ℝ) + 4) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num]
    simp only [Real.log_pow]
    push_cast
    ring
  have hVle : (2 * (q : ℝ) + 5) ^ 6 / (9 * ((q : ℝ) + 4) ^ 4) ≤
      ((q : ℝ) + 2) ^ ((3000 : ℝ) / 1084) := by
    rw [Real.le_rpow_iff_log_le hV (by linarith), hlogV]
    linarith [gcw_sharp_log_bound q hq]
  have hright :
      (((q : ℝ) + 2) ^ ((1000 : ℝ) / 1084)) ^ 3 = ((q : ℝ) + 2) ^ ((3000 : ℝ) / 1084) := by
    rw [← Real.rpow_natCast (((q : ℝ) + 2) ^ ((1000 : ℝ) / 1084)) 3,
      ← Real.rpow_mul (by linarith)]
    norm_num
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
  rw [hright, hcube, hrat]
  exact hVle

/-- **The `q = 1` certificate is below `3^{1000/1084}`**:

```text
474609871/172265625 = 2.7551049…  ≤  3^{1000/1084} = 2.7551723…
```

the one place where the eight-digit enclosures are indispensable: the two sides differ by
`2.4·10⁻⁵` in the logarithm, which the six-digit enclosures of `log 3` cannot resolve.  From
`log_gcwOneCertificate_le_sharp` (`≤ 1.0134555265`) and `log_three_ge_sharp`
(`(1000/1084)·1.0986122886 = 1.0134799…`). -/
theorem gcwOneCertificate_le_rpow :
    (474609871 : ℝ) / 172265625 ≤ (3 : ℝ) ^ ((1000 : ℝ) / 1084) := by
  rw [Real.le_rpow_iff_log_le (by norm_num) (by norm_num)]
  linarith [log_gcwOneCertificate_le_sharp, log_three_ge_sharp]

end SharpNumeric

section SharpBarrier

open AlgebraicComplexity.Analysis

variable {K : Type u} [Field K] {μ : Type} [Fintype μ] [DecidableEq μ]

/-- **The geometric lower bound on the asymptotic ranks of the powers**, `(q+2)^n ≤ R̃(CW^{⊗n})`,
factored out of the barrier proofs: conciseness `q + 2 ≤ R̃(CW_q^σ)`
(`card_le_asymptoticRank_gcwTable`) powered up by
`asymptoticRank_pow_le_of_isCoordinateConcise`. -/
theorem gcw_card_pow_le_asymptoticRank_power (σ : Equiv.Perm μ) (n : ℕ) :
    ((Fintype.card μ : ℝ) + 2) ^ n ≤
      Tensor.asymptoticRank (Tensor.power (coordinateTensor (gcwTable K μ σ)) n) := by
  have hconc : ∀ i, Tensor.IsCoordinateConcise (gcwTable K μ σ) i :=
    fun i ↦ isCoordinateConcise_gcwTable K σ i
  calc ((Fintype.card μ : ℝ) + 2) ^ n
      ≤ Tensor.asymptoticRank (coordinateTensor (gcwTable K μ σ)) ^ n :=
        pow_le_pow_left₀ (by positivity) (card_le_asymptoticRank_gcwTable (K := K) σ) n
    _ ≤ Tensor.asymptoticRank (Tensor.power (coordinateTensor (gcwTable K μ σ)) n) :=
        asymptoticRank_pow_le_of_isCoordinateConcise K hconc n

/-- **`S̃(CW_q^σ) ≤ (q+2)^{1000/1084}`** for every `q ≥ 1` and every `σ`, the sharp-exponent form
of `asymptoticSliceRank_gcwTable_le_rpow`.

The exponent `1000/1084 = 0.92250922…` is above the sharp `0.92248856…` of [Alman2019] at `q = 1`
and below `12/13`.  Two parameters are used: the cube `u = (21/25)³` at `q = 1`, where the
rational family `3/(q+4)` would miss by `10⁻⁵`, and the family itself at `q ≥ 2`. -/
theorem asymptoticSliceRank_gcwTable_le_rpow_sharp (σ : Equiv.Perm μ)
    (hq : 1 ≤ Fintype.card μ) :
    Tensor.asymptoticSliceRank (coordinateTensor (gcwTable K μ σ)) ≤
      ((Fintype.card μ : ℝ) + 2) ^ ((1000 : ℝ) / 1084) := by
  rcases eq_or_lt_of_le hq with h1 | h2
  · have hcard : ((Fintype.card μ : ℕ) : ℝ) = 1 := by exact_mod_cast h1.symm
    have hb := asymptoticSliceRank_gcwTable_le_rpow_mul (K := K) σ hq
      (u := (9261 : ℝ) / 15625) (by norm_num)
    have hroot : ((9261 : ℝ) / 15625) ^ ((3 : ℝ)⁻¹) = 21 / 25 := by
      rw [show (9261 : ℝ) / 15625 = ((21 : ℝ) / 25) ^ (3 : ℕ) by norm_num]
      simpa using Real.pow_rpow_inv_natCast (x := (21 : ℝ) / 25) (n := 3) (by norm_num)
        (by norm_num)
    rw [hcard, hroot] at hb
    rw [hcard, show (1 : ℝ) + 2 = 3 by norm_num]
    refine hb.trans (le_trans (le_of_eq ?_) gcwOneCertificate_le_rpow)
    norm_num
  · refine le_trans (asymptoticSliceRank_gcwTable_le_rpow_mul (K := K) σ hq
      (u := (3 : ℝ) / ((Fintype.card μ : ℝ) + 4)) (by positivity)) ?_
    exact gcw_sharp_rpow_mul_le_rpow (Fintype.card μ) h2

/-- **[Alman2019, Theorem 5.7] with the constant `2.168`, unconditionally.**  For every field `K`,
every parameter `q ≥ 1` and every middle permutation `σ`, the Universal method applied to the
generalized Coppersmith--Winograd tensor `CW_q^σ` cannot prove any bound on `ω` below `2.168`:

```text
ω_u(CW_{q,σ}) ≥ 21680/10000 = 2.168.
```

This is `13/6 = 2.1666…` sharpened by `1.3·10⁻³`, and it is within `5.3·10⁻⁵` of the thesis
constant `2.1680525…`, which is a `q = 1` statement and is proved as such in
`thesis_constant_le_universalExponent_gcwTable_card_one` below.

Corollary 5.2 (`two_div_le_universalExponent_of_asymptoticSliceRank`) with `R = q+2`,
`S = (q+2)^{1000/1084}` and `s = 1000/1084`, whose `2/s` is exactly `2.168`; the slice-rank input
is `asymptoticSliceRank_gcwTable_le_rpow_sharp` and the rank input
`gcw_card_pow_le_asymptoticRank_power`.  The obligation is discharged by
`Tensor.sliceRankDegenerationMonotone_holds`; `hne` is necessary for the same reason as in
`thirteen_div_six_le_universalExponent_gcwTable`. -/
theorem avw_thesis_constant_le_universalExponent_gcwTable (σ : Equiv.Perm μ)
    (hq : 1 ≤ Fintype.card μ)
    (hne : (universalValues K (coordinateTensor (gcwTable K μ σ))).Nonempty) :
    (21680 : ℝ) / 10000 ≤ universalExponent K (coordinateTensor (gcwTable K μ σ)) := by
  have hqR : (1 : ℝ) ≤ (Fintype.card μ : ℝ) := by exact_mod_cast hq
  have hR : (0 : ℝ) < (Fintype.card μ : ℝ) + 2 := by linarith
  have hS : (1 : ℝ) < ((Fintype.card μ : ℝ) + 2) ^ ((1000 : ℝ) / 1084) :=
    Real.one_lt_rpow_iff_of_pos hR |>.mpr (Or.inl ⟨by linarith, by norm_num⟩)
  have hmain := two_div_le_universalExponent_of_asymptoticSliceRank K
    (Tensor.sliceRankDegenerationMonotone_holds K)
    (T := coordinateTensor (gcwTable K μ σ)) (R := (Fintype.card μ : ℝ) + 2)
    (S := ((Fintype.card μ : ℝ) + 2) ^ ((1000 : ℝ) / 1084)) (s := (1000 : ℝ) / 1084)
    hne hR hS (by norm_num) le_rfl (fun n _ ↦ gcw_card_pow_le_asymptoticRank_power σ n)
    (asymptoticSliceRank_gcwTable_le_rpow_sharp σ hq)
  rwa [show (2 : ℝ) / ((1000 : ℝ) / 1084) = 21680 / 10000 by norm_num] at hmain

/-- **The thesis constant itself**: for `q = 1`,

```text
ω_u(CW_{1,σ}) ≥ 2.16805229,
```

against the printed `2 log 3 / log 2.7551046… = 2.1680525…` of [Alman2019, Theorem 5.7].  The
eight certified digits are all the enclosures support: the margin at `2.16805229` is `2.1·10⁻⁹`.

Theorem 5.1 in its printed form `ω_u ≥ 2 log R̃ / log S̃` with `R̃ ≥ 3` and the rational
block-entropy certificate `S̃(CW_1^σ) ≤ 474609871/172265625` at `u = (21/25)³`, then
`log_gcwOneCertificate_le_sharp` and `log_three_ge_sharp`.  Unconditional. -/
theorem thesis_constant_le_universalExponent_gcwTable_card_one (σ : Equiv.Perm μ)
    (hcard : Fintype.card μ = 1)
    (hne : (universalValues K (coordinateTensor (gcwTable K μ σ))).Nonempty) :
    (216805229 : ℝ) / 100000000 ≤ universalExponent K (coordinateTensor (gcwTable K μ σ)) := by
  have hcardR : ((Fintype.card μ : ℕ) : ℝ) = 1 := by exact_mod_cast hcard
  have hq : 1 ≤ Fintype.card μ := by omega
  have hSle : Tensor.asymptoticSliceRank (coordinateTensor (gcwTable K μ σ)) ≤
      474609871 / 172265625 := by
    have hb := asymptoticSliceRank_gcwTable_le_rpow_mul (K := K) σ hq
      (u := (9261 : ℝ) / 15625) (by norm_num)
    have hroot : ((9261 : ℝ) / 15625) ^ ((3 : ℝ)⁻¹) = 21 / 25 := by
      rw [show (9261 : ℝ) / 15625 = ((21 : ℝ) / 25) ^ (3 : ℕ) by norm_num]
      simpa using Real.pow_rpow_inv_natCast (x := (21 : ℝ) / 25) (n := 3) (by norm_num)
        (by norm_num)
    rw [hcardR, hroot] at hb
    refine hb.trans (le_of_eq ?_)
    norm_num
  have hRle : ∀ n : ℕ, 1 ≤ n →
      (3 : ℝ) ^ n ≤
        Tensor.asymptoticRank (Tensor.power (coordinateTensor (gcwTable K μ σ)) n) := by
    intro n _
    have h := gcw_card_pow_le_asymptoticRank_power (K := K) σ n
    rwa [hcardR, show (1 : ℝ) + 2 = 3 by norm_num] at h
  have hmain := two_mul_log_div_log_le_universalExponent_of_asymptoticSliceRank K
    (Tensor.sliceRankDegenerationMonotone_holds K) hne (R := (3 : ℝ))
    (S := (474609871 : ℝ) / 172265625) (by norm_num) (by norm_num) hRle hSle
  refine le_trans ?_ hmain
  have hlog : (0 : ℝ) < Real.log ((474609871 : ℝ) / 172265625) := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog]
  linarith [log_gcwOneCertificate_le_sharp, log_three_ge_sharp]

/-- **The `q = 5` entry of the thesis table**:

```text
ω_u(CW_{5,σ}) ≥ 2.21912378,
```

against the printed `2.21912…` of [Alman2019].  Same argument as for `q = 1`, with `R̃ ≥ 7` and
the rational block-entropy certificate `S̃(CW_5^σ) ≤ 127218805/22024249` at `u = (13/19)³`
(`5.7763061…` against the sharp `5.77628514…`), through `log_gcwFiveCertificate_le_sharp` and
`log_seven_ge_sharp`.  Unconditional. -/
theorem thesis_constant_le_universalExponent_gcwTable_card_five (σ : Equiv.Perm μ)
    (hcard : Fintype.card μ = 5)
    (hne : (universalValues K (coordinateTensor (gcwTable K μ σ))).Nonempty) :
    (221912378 : ℝ) / 100000000 ≤ universalExponent K (coordinateTensor (gcwTable K μ σ)) := by
  have hcardR : ((Fintype.card μ : ℕ) : ℝ) = 5 := by exact_mod_cast hcard
  have hq : 1 ≤ Fintype.card μ := by omega
  have hSle : Tensor.asymptoticSliceRank (coordinateTensor (gcwTable K μ σ)) ≤
      127218805 / 22024249 := by
    have hb := asymptoticSliceRank_gcwTable_le_rpow_mul (K := K) σ hq
      (u := (2197 : ℝ) / 6859) (by norm_num)
    have hroot : ((2197 : ℝ) / 6859) ^ ((3 : ℝ)⁻¹) = 13 / 19 := by
      rw [show (2197 : ℝ) / 6859 = ((13 : ℝ) / 19) ^ (3 : ℕ) by norm_num]
      simpa using Real.pow_rpow_inv_natCast (x := (13 : ℝ) / 19) (n := 3) (by norm_num)
        (by norm_num)
    rw [hcardR, hroot] at hb
    refine hb.trans (le_of_eq ?_)
    norm_num
  have hRle : ∀ n : ℕ, 1 ≤ n →
      (7 : ℝ) ^ n ≤
        Tensor.asymptoticRank (Tensor.power (coordinateTensor (gcwTable K μ σ)) n) := by
    intro n _
    have h := gcw_card_pow_le_asymptoticRank_power (K := K) σ n
    rwa [hcardR, show (5 : ℝ) + 2 = 7 by norm_num] at h
  have hmain := two_mul_log_div_log_le_universalExponent_of_asymptoticSliceRank K
    (Tensor.sliceRankDegenerationMonotone_holds K) hne (R := (7 : ℝ))
    (S := (127218805 : ℝ) / 22024249) (by norm_num) (by norm_num) hRle hSle
  refine le_trans ?_ hmain
  have hlog : (0 : ℝ) < Real.log ((127218805 : ℝ) / 22024249) := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog]
  linarith [log_gcwFiveCertificate_le_sharp, log_seven_ge_sharp]

end SharpBarrier

end Sharp

end AlgebraicComplexity.Examples
