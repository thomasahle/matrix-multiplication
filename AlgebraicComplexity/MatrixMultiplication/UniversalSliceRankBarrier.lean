/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.IndependentDiagonal
import AlgebraicComplexity.MatrixMultiplication.UniversalMethod
import AlgebraicComplexity.Tensor.SliceRankDegeneration

/-!
# The asymptotic-slice-rank barrier for the Universal method

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module instantiates the
abstract-measure barrier theorem of `MatrixMultiplication/UniversalMethod.lean` with the
asymptotic slice rank `S̃` of `Tensor/AsymptoticSliceRank.lean`, obtaining Theorem 5.1 and
Corollary 5.2 of

> J. Alman, *Limits on the Universal Method for Matrix Multiplication*, PhD thesis, MIT, 2019
> (see also CCC 2019),

hereafter [Alman2019], in the form in which they are printed:

```text
ω_u(T) ≥ 2·log R̃(T) / log S̃(T),        and        S̃(T) ≤ R̃(T)^s with s < 1  ⟹  ω_u(T) ≥ 2/s > 2.
```

## The three inputs, and where each comes from

`two_mul_log_div_log_le_universalExponent_of_measure` asks for a "measure" of the powers of `T`
and of the square matrix-multiplication tensors satisfying three properties.  With
`fPower n = S̃(T^{⊗n})` and `fMM q = S̃(⟨q,q,q⟩)`:

* **degeneration monotonicity** `S̃(⟨q,q,q⟩) ≤ S̃(T^{⊗n})` for a universal certificate: this is
  `Tensor.asymptoticSliceRank_polynomialDegenerates_le` (thesis Proposition 5.1, quoting
  [TaoSawin2016, Corollary 2]).  It was the one unproved ingredient while the saturation step was
  missing; it is now a theorem over every field
  (`Tensor.sliceRankDegenerationMonotone_holds`, proved in `Tensor/SliceRankSaturation.lean`), so
  every result in this module is unconditional.  The theorems of the `Barrier` section below still
  *accept* the packaged obligation `Tensor.SliceRankDegenerationMonotone` as a hypothesis, purely
  for source compatibility with the branches written while it was open; the `Unconditional` section
  restates the endpoints without it.
* **submultiplicativity along powers** `S̃(T^{⊗n}) ≤ S̃(T)^n`: this is
  `Tensor.asymptoticSliceRank_power_le_pow`, proved unconditionally (it is the half of the power
  law that a `limsup` gives for free).
* **the matrix-multiplication value** `q² ≤ S̃(⟨q,q,q⟩)`: the lower half of thesis Corollary 5.1.
  It is obtained here from the *independence number* rather than from a direct slice-rank
  argument: `Ī(⟨q,q,q⟩) = q²` (`asymptoticIndependenceNumber_mmCoefficients_self`, AVW Lemma 4.4)
  and `Ī ≤ S̃` (`Tensor.asymptoticIndependenceNumber_le_asymptoticSliceRank`, which factors
  through `Q̃ ≤ S̃`).  Note that only this inequality is needed, not Alman's equality
  `Q̃(⟨q,q,q⟩) = S̃(⟨q,q,q⟩) = q²`.

## Main results

* `sq_le_asymptoticSliceRank_matrixMultiplication`: `q² ≤ S̃(⟨q,q,q⟩)`.
* `universalCertificate_sq_le_pow_of_asymptoticSliceRank_le`: the hypothesis `q² ≤ S^n` of
  Theorem 5.1, discharged from any upper bound `S̃(T) ≤ S`.
* `two_mul_log_div_log_le_universalExponent_of_asymptoticSliceRank`: **Theorem 5.1** with abstract
  bounds `R ≤ R̃`, `S̃ ≤ S`.
* `two_mul_log_asymptoticRank_div_log_asymptoticSliceRank_le_universalExponent`: **Theorem 5.1**
  as printed, `ω_u(T) ≥ 2·log R̃(T)/log S̃(T)`.
* `two_div_le_universalExponent_of_asymptoticSliceRank`, and its strict form
  `two_lt_universalExponent_of_asymptoticSliceRank`: **Corollary 5.2**, `2/s ≤ ω_u(T)` and
  `2 < ω_u(T)`.

## Why a separate module

`MatrixMultiplication/UniversalMethod.lean` deliberately does not mention slice rank: its
Theorem 5.1 is stated against two abstract measure sequences so that the universal-method
development does not depend on the slice-rank tower.  Keeping the instantiation here preserves
that separation: the abstract barrier theorem stays free of the slice-rank tower, and the
slice-rank instantiation lives with the results that need it.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

section Barrier

variable (K : Type u) [Field K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **`q² ≤ S̃(⟨q,q,q⟩)`**, the lower half of thesis Corollary 5.1 in the only form the barrier
needs.

Proof sketch: `Ī(⟨q,q,q⟩) = q²` (`asymptoticIndependenceNumber_mmCoefficients_self`) and the
asymptotic independence number of a coefficient table never exceeds the asymptotic slice rank of
the tensor it defines (`Tensor.asymptoticIndependenceNumber_le_asymptoticSliceRank`), while
`coordinateTensor_mmCoefficients` identifies that tensor with `⟨q,q,q⟩`. -/
theorem sq_le_asymptoticSliceRank_matrixMultiplication (q : ℕ) :
    (q : ℝ) ^ 2 ≤ asymptoticSliceRank (matrixMultiplication (K := K) q q q) := by
  have h := asymptoticIndependenceNumber_le_asymptoticSliceRank (mmCoefficients K q q q)
  rwa [asymptoticIndependenceNumber_mmCoefficients_self, coordinateTensor_mmCoefficients] at h

/-- **The slice-rank hypothesis of Theorem 5.1, discharged.**  If `S̃(T) ≤ S` then every universal
certificate `(n,q)` of `T` satisfies `q² ≤ S^n`.

This is the chain `q² ≤ S̃(⟨q,q,q⟩) ≤ S̃(T^{⊗n}) ≤ S̃(T)^n ≤ S^n`: the value of the target,
degeneration monotonicity (thesis Proposition 5.1, now proved --- see
`Tensor.asymptoticSliceRank_polynomialDegenerates_le`), the power law, and the hypothesis.
Unconditional. -/
theorem universalCertificate_sq_le_pow_of_asymptoticSliceRank_le
    {T : Tensor3 K V} {S : ℝ} (hSle : asymptoticSliceRank T ≤ S)
    (n q : ℕ) (hcert : UniversalCertificate K T n q) : (q : ℝ) ^ 2 ≤ S ^ n := by
  have h1 : (q : ℝ) ^ 2 ≤ asymptoticSliceRank (matrixMultiplication (K := K) q q q) :=
    sq_le_asymptoticSliceRank_matrixMultiplication K q
  have h2 : asymptoticSliceRank (matrixMultiplication (K := K) q q q) ≤
      asymptoticSliceRank (Tensor.power T n) :=
    asymptoticSliceRank_polynomialDegenerates_le hcert
  have h3 : asymptoticSliceRank (Tensor.power T n) ≤ asymptoticSliceRank T ^ n :=
    asymptoticSliceRank_power_le_pow T n
  have h4 : asymptoticSliceRank T ^ n ≤ S ^ n :=
    pow_le_pow_left₀ (asymptoticSliceRank_nonneg T) hSle n
  linarith

/-- **Theorem 5.1** ([Alman2019], §5.2) for the asymptotic slice rank, with abstract bounds: if
`R` is a geometric lower bound for the asymptotic ranks of the powers of `T` (think `R = R̃(T)`)
and `S̃(T) ≤ S` with `S > 1`, then

```text
ω_u(T) ≥ 2·log R / log S.
```

The hypothesis `_hobl` is no longer needed: `Tensor.SliceRankDegenerationMonotone` is a theorem
(`Tensor.sliceRankDegenerationMonotone_holds`).  It is retained only so that existing call sites
keep compiling; new clients should use the `Unconditional` section below. -/
theorem two_mul_log_div_log_le_universalExponent_of_asymptoticSliceRank
    (_hobl : SliceRankDegenerationMonotone.{u, max u v, u} K)
    {T : Tensor3 K V} {R S : ℝ}
    (hne : (universalValues K T).Nonempty) (hR : 0 < R) (hS : 1 < S)
    (hRle : ∀ n : ℕ, 1 ≤ n → R ^ n ≤ asymptoticRank (Tensor.power T n))
    (hSle : asymptoticSliceRank T ≤ S) :
    2 * Real.log R / Real.log S ≤ universalExponent K T :=
  two_mul_log_div_log_le_universalExponent K hne hR hS hRle
    fun n q _ _ hcert ↦
      universalCertificate_sq_le_pow_of_asymptoticSliceRank_le K hSle n q hcert

/-- **Theorem 5.1 as printed** ([Alman2019], §5.2):

```text
ω_u(T) ≥ 2·log R̃(T) / log S̃(T).
```

The hypothesis `hone` (every power of `T` is non-zero) is the nondegeneracy condition under which
`R̃(T)^n ≤ R̃(T^{⊗n})` is available in this repository
(`Tensor.asymptoticRank_pow_le_asymptoticRank_power`); `hSpos` excludes the degenerate case
`S̃(T) ≤ 1`, where the right-hand side is not defined by this formula.

The hypothesis `_hobl` is no longer needed: `Tensor.SliceRankDegenerationMonotone` is a theorem
(`Tensor.sliceRankDegenerationMonotone_holds`).  It is retained only for source compatibility; the
`Unconditional` section below states this theorem without it. -/
theorem two_mul_log_asymptoticRank_div_log_asymptoticSliceRank_le_universalExponent
    (_hobl : SliceRankDegenerationMonotone.{u, max u v, u} K)
    {T : Tensor3 K V}
    (hne : (universalValues K T).Nonempty)
    (hone : ∀ m : ℕ, 1 ≤ Tensor.rank (Tensor.power T m))
    (hRpos : 0 < asymptoticRank T) (hSpos : 1 < asymptoticSliceRank T) :
    2 * Real.log (asymptoticRank T) / Real.log (asymptoticSliceRank T) ≤ universalExponent K T :=
  two_mul_log_div_log_le_universalExponent_of_asymptoticSliceRank K _hobl hne hRpos hSpos
    (fun n _ ↦ asymptoticRank_pow_le_asymptoticRank_power T hone n) le_rfl

/-- **Corollary 5.2** ([Alman2019], §5.2) for the asymptotic slice rank: if the asymptotic slice
rank is at most `R^s` for a geometric lower bound `R` on the asymptotic ranks of the powers, then
`ω_u(T) ≥ 2/s`.

The hypothesis `_hobl` is no longer needed: `Tensor.SliceRankDegenerationMonotone` is a theorem
(`Tensor.sliceRankDegenerationMonotone_holds`).  It is retained only for source compatibility. -/
theorem two_div_le_universalExponent_of_asymptoticSliceRank
    (_hobl : SliceRankDegenerationMonotone.{u, max u v, u} K)
    {T : Tensor3 K V} {R S s : ℝ}
    (hne : (universalValues K T).Nonempty) (hR : 0 < R) (hS : 1 < S)
    (hs : 0 < s) (hSR : S ≤ R ^ s)
    (hRle : ∀ n : ℕ, 1 ≤ n → R ^ n ≤ asymptoticRank (Tensor.power T n))
    (hSle : asymptoticSliceRank T ≤ S) :
    2 / s ≤ universalExponent K T :=
  two_div_le_universalExponent K hne hR hS hs hSR hRle
    fun n q _ _ hcert ↦
      universalCertificate_sq_le_pow_of_asymptoticSliceRank_le K hSle n q hcert

/-- **Corollary 5.2, final form** ([Alman2019], §5.2): an asymptotic slice rank that is a strictly
sublinear power of the asymptotic rank forces `ω_u(T) > 2`, so the Universal method applied to `T`
cannot prove `ω = 2`.

The hypothesis `_hobl` is no longer needed: `Tensor.SliceRankDegenerationMonotone` is a theorem
(`Tensor.sliceRankDegenerationMonotone_holds`).  It is retained only for source compatibility. -/
theorem two_lt_universalExponent_of_asymptoticSliceRank
    (_hobl : SliceRankDegenerationMonotone.{u, max u v, u} K)
    {T : Tensor3 K V} {R S s : ℝ}
    (hne : (universalValues K T).Nonempty) (hR : 0 < R) (hS : 1 < S)
    (hs : 0 < s) (hs1 : s < 1) (hSR : S ≤ R ^ s)
    (hRle : ∀ n : ℕ, 1 ≤ n → R ^ n ≤ asymptoticRank (Tensor.power T n))
    (hSle : asymptoticSliceRank T ≤ S) :
    2 < universalExponent K T :=
  two_lt_universalExponent K hne hR hS hs hs1 hSR hRle
    fun n q _ _ hcert ↦
      universalCertificate_sq_le_pow_of_asymptoticSliceRank_le K hSle n q hcert

end Barrier
section Unconditional

/-! ### Unconditional forms

`Tensor.sliceRankDegenerationMonotone_holds` (Tao–Sawin monotonicity, proved in
`Tensor/SliceRankSaturation.lean`) discharges the obligation hypothesis, which the `Barrier`
section retains only for source compatibility. -/

variable {K : Type u} [Field K]

/-- Theorem 5.1 of [Alman2019], unconditionally: `2·log R̃(T) / log S̃(T) ≤ ω_u(T)`. -/
theorem two_mul_log_asymptoticRank_div_log_asymptoticSliceRank_le_universalExponent'
    {V : Leg → Type v} [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)] {T : Tensor3 K V}
    (hne : (universalValues K T).Nonempty)
    (hone : ∀ m, 1 ≤ Tensor.rank (Tensor.power T m)) (hR : 0 < Tensor.asymptoticRank T)
    (hS : 1 < Tensor.asymptoticSliceRank T) :
    2 * Real.log (Tensor.asymptoticRank T) / Real.log (Tensor.asymptoticSliceRank T) ≤
      universalExponent K T :=
  two_mul_log_asymptoticRank_div_log_asymptoticSliceRank_le_universalExponent K
    (Tensor.sliceRankDegenerationMonotone_holds K) hne hone hR hS

end Unconditional

end AlgebraicComplexity
