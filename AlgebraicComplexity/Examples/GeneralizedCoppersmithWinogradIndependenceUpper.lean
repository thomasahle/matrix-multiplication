/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSupport
import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinogradIndependenceLower
import AlgebraicComplexity.Tensor.IndependenceBlockEntropy

/-!
# The block-entropy upper bound on `Ī(CW_q^σ)`

This file instantiates the block-partition entropy bound
`Tensor.asymptoticIndependenceNumber_le_of_blockEntropy` (Alman's Theorem 5.3, see
`Tensor/IndependenceBlockEntropy.lean`) on the generalized Coppersmith--Winograd tensors

```text
CW_q^σ = x₀y₀z_{q+1} + x₀y_{q+1}z₀ + x_{q+1}y₀z₀ + ∑ᵢ (xᵢy_{σ(i)}z₀ + xᵢy₀zᵢ + x₀yᵢzᵢ)
```

of [AlmanVassilevskaWilliams2018, Definition 3.1], with the classical six-block partition of
[Alman2019, §5.5.1]: each leg is split into `{0}`, `{1,…,q}` and `{q+1}`, and the six non-zero
blocks are `T₂₀₀, T₀₂₀, T₀₀₂, T₀₁₁, T₁₀₁, T₁₁₀`.

## Main results

* `asymptoticIndependenceNumber_gcwTable_le_rpow_mul` (**the headline analytic bound**): for every
  `q ≥ 1`, every `σ`, and every real `u > 0`,

  ```text
  Ī(CW_q^σ) ≤ u^{1/3} · (q + u + 1/u).
  ```

  Minimizing the right-hand side over `u` reproduces Alman's value
  `S̃(CW_{q,σ}) = sup_{v ∈ [0,1/3]} q^{2(1/3−v)} / (v^v (2/3−2v)^{2/3−2v} (1/3+v)^{1/3+v})`
  numerically: at `q = 1` the optimum is `2.7551…`, at `q = 6` it is `6.44493…`, matching the table
  on p. 71 of [Alman2019] --- see the discussion of the two forms below.
* `asymptoticIndependenceNumber_gcwTable_le_of_reference`: the general form of which the previous
  theorem is the optimally-tuned case.  For `q ≥ 1` and every probability vector `r` with positive
  weights on the three blocks `{0}`, `{1,…,q}`, `{q+1}` satisfying
  `(q/r_middle)² ≤ (1/r_last)·(1/r_zero)`, every `M ≥ 0` with
  `(1/r_last)·(1/r_zero)² ≤ M³` bounds `Ī(CW_q^σ) ≤ M`.
* `asymptoticIndependenceNumber_gcwTable_fin_six_le` (**the certified numeric instance**):
  `Ī(CW_6^σ) ≤ 6.45` for every permutation `σ` of `{1,…,6}` and every coefficient semiring without
  zero divisors, from the rational certificate `u = (13/20)³`, whose value is `6.4453701…`.
  Alman's exact value is `6.44493…`.
* `asymptoticIndependenceNumber_gcwTable_fin_one_le`: the same at the other end of Alman's table,
  `Ī(CW_1^σ) ≤ 2.7552` against his exact `2.7551…`.
* `avw_gcwTable_independence_sandwich_upper_fin_six`: the sandwich
  `6 + 6/25 ≤ Ī(CW_6^σ) ≤ 6.45`, sharpening
  `avw_gcwTable_independence_sandwich_fin_six`, whose upper bound was `Ī(CW_6^σ) < 8`.
* `gcwBlockLegValue_le_of_reference`, `gcwBlockLegValue_le_rpow_mul`,
  `gcwBlockLegValue_fin_six_le`, `gcwBlockLegValue_fin_one_le`: the underlying **block value
  certificates**, which are statements about the six-block partition alone and mention neither the
  coefficient semiring nor the invariant being bounded.  Each `Ī` bound above is one application of
  `Tensor.asymptoticIndependenceNumber_le_of_blockEntropy` to the corresponding certificate, and
  `Examples/GeneralizedCoppersmithWinogradSliceRankUpper.lean` reuses the same four certificates for
  the asymptotic slice rank `S̃`, which is what Alman actually bounds.
* `coordinateGalacticExponent_gcwTable_fin_six_ge`: the resulting barrier.  Since
  `R̃(CW_6^σ) ≥ 8` and `6.45 ≤ 8^{26/29}`, AVW Corollary 4.3 gives

  ```text
  ω_g^{coord}(CW_6^σ) ≥ 6/(26/29 + 2) = 29/14 = 2.0714…
  ```

  in place of the previously proved `60000/29999 = 2.00006…`.

## Why a reference vector replaces the supremum over the simplex

Alman's Theorem 5.3 bounds `Ī` by a supremum over all probability distributions `p` on the six
non-zero blocks of `min{p_X, p_Y, p_Z}`, and his Proposition 5.4 restricts that supremum to the
`CW`-symmetric `p`, a one-parameter family `p(corner) = v`, `p(middle) = 1/3 − v`.  The resulting
sup over `v ∈ [0,1/3]` is the displayed expression above; it has no closed form (its optimizer is
the root of `(2/3−2v)² = q²·v·(1/3+v)`), so a *certified numerical* upper bound on it needs either
a calculus argument or an interval subdivision.

The reference-vector form of the entropy bound
(`blockLegValue_le_prod_rpow`, Gibbs' inequality) avoids all of that, and simultaneously
avoids Proposition 5.4.  For any full-support probability vector `r` on `{zero, middle, last}`,

```text
p_c ≤ ∏_a (|X_a| / r_a)^{p_c(a)}   for each leg c,
```

and the right-hand side is *log-linear* in the marginal `p_c`.  Multiplying the three legs, all
dependence on `p` collapses into the single number `A = p(T₂₀₀)+p(T₀₂₀)+p(T₀₀₂)`, the total corner
mass (Alman's `3v`):

```text
p_X · p_Y · p_Z ≤ (1/r_last)^A · (q/r_middle)^{2−2A} · (1/r_zero)^{1+A},
```

which is a *geometric* function of `A ∈ [0,1]` and is therefore maximized at an endpoint.  This is
Legendre duality: as `r` ranges over the simplex, the family of bounds obtained this way has
infimum exactly Alman's supremum, and choosing `r` to be the optimal marginal makes the bound
tight.  The specialization `r_last = t·u`, `r_middle = q·t`, `r_zero = t/u` with
`t = 1/(q + u + 1/u)` makes the two endpoints coincide (the geometric ratio is `1`) and yields the
closed form `u^{1/3}(q + u + 1/u)` for every `u > 0`.

Consequently:

* Alman's Proposition 5.4 is **not used**; symmetrization is unnecessary, because the bound already
  depends on `p` only through `A`.  (Its convexity kernel `a^a b^b c^c ≥ d^{3d}` is in any case a
  one-line consequence of `blockLegValue_le_sum` applied to the uniform weights on `Leg`.)
* The literal statement `Ī(CW_q^σ) ≤ sup_{v ∈ [0,1/3]} …` is **not** formalized; the `u`-family
  above is its exact dual and is what the numerical certificate uses.

## Position in the library

Layer 4 (`AlgebraicComplexity/Examples/`), a named client.  Besides the layer-1 entropy bound it
imports the generalized CW family and its independence lower bounds; the barrier consequence uses
the conciseness and asymptotic-rank facts of `Examples/GeneralizedCoppersmithWinogradBarrier.lean`
and AVW Corollary 4.3 from `MatrixMultiplication/IndependenceBarrier.lean`.

The coarse block labelling `gcwCoarseLabelling` is the legwise form of the shared coordinate block
label `gcwBlockLabel`, which lives next to `gcwTable` in
`Examples/GeneralizedCoppersmithWinograd.lean`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-! ## The six-block partition of `CW_q^σ` -/

section Partition

variable {μ : Type} [Fintype μ] [DecidableEq μ]

/-- The legwise coarse block labelling of `CW_q^σ`, built from the shared coordinate block label
`gcwBlockLabel` of `Examples/GeneralizedCoppersmithWinograd.lean`: `0` and `q+1` are their own
blocks and `{1,…,q}` is the middle block.  This is the block labelling of the classical CW
partition, in the sense of `Tensor/CoordinateBlockWord.lean`. -/
def gcwCoarseLabelling (μ : Type) : ∀ c : Leg, GenCWIndexFamily μ c → CWBlock :=
  fun _ ↦ gcwBlockLabel μ

/-- The index type of the six non-zero blocks of the CW partition: `Sum.inl c` is the corner block
carrying `q+1` on leg `c` and `0` on the other two legs (`T₂₀₀`, `T₀₂₀`, `T₀₀₂`), and `Sum.inr c` is
the middle block carrying `0` on leg `c` and `{1,…,q}` on the other two (`T₀₁₁`, `T₁₀₁`, `T₁₁₀`). -/
abbrev GcwBlockIndex := Leg ⊕ Leg

/-- The block address of one of the six non-zero blocks. -/
def gcwBlockAddress : GcwBlockIndex → CWBlockAddress
  | .inl c => fun c' ↦ if c' = c then CWBlock.last else CWBlock.zero
  | .inr c => fun c' ↦ if c' = c then CWBlock.zero else CWBlock.middle

/-- **The six non-zero blocks cover the support of `CW_q^σ`.**  Each of the `3q+3` terms of
[AlmanVassilevskaWilliams2018, Definition 3.1] has one of the six block addresses
`T₂₀₀, T₀₂₀, T₀₀₂, T₀₁₁, T₁₀₁, T₁₁₀`. -/
theorem gcwTable_blockCover {K : Type u} [CommSemiring K] [Nontrivial K] (σ : Equiv.Perm μ)
    (s : ∀ c, GenCWIndexFamily μ c) (hs : gcwTable K μ σ s ≠ 0) :
    ∃ j : GcwBlockIndex, ∀ c, gcwCoarseLabelling μ c (s c) = gcwBlockAddress j c := by
  rcases (gcwTable_ne_zero_iff σ s).mp hs with
    ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
    ⟨i, hx, hy, hz⟩ | ⟨i, hx, hy, hz⟩ | ⟨i, hx, hy, hz⟩
  · exact ⟨.inl Leg.Z, fun c ↦ by
      cases c <;> simp [gcwCoarseLabelling, gcwBlockLabel, gcwBlockAddress, hx, hy, hz]⟩
  · exact ⟨.inl Leg.Y, fun c ↦ by
      cases c <;> simp [gcwCoarseLabelling, gcwBlockLabel, gcwBlockAddress, hx, hy, hz]⟩
  · exact ⟨.inl Leg.X, fun c ↦ by
      cases c <;> simp [gcwCoarseLabelling, gcwBlockLabel, gcwBlockAddress, hx, hy, hz]⟩
  · exact ⟨.inr Leg.Z, fun c ↦ by
      cases c <;> simp [gcwCoarseLabelling, gcwBlockLabel, gcwBlockAddress, hx, hy, hz]⟩
  · exact ⟨.inr Leg.Y, fun c ↦ by
      cases c <;> simp [gcwCoarseLabelling, gcwBlockLabel, gcwBlockAddress, hx, hy, hz]⟩
  · exact ⟨.inr Leg.X, fun c ↦ by
      cases c <;> simp [gcwCoarseLabelling, gcwBlockLabel, gcwBlockAddress, hx, hy, hz]⟩

/-- **The three block sizes.**  On every leg the blocks `0` and `q+1` are singletons and the middle
block has `q` elements. -/
theorem blockFiberCard_gcwCoarseLabelling (c : Leg) (a : CWBlock) :
    Tensor.blockFiberCard (κ := GenCWIndexFamily μ) (gcwCoarseLabelling μ) c a =
      if a = CWBlock.middle then Fintype.card μ else 1 := by
  classical
  cases a with
  | zero =>
      have : WordType.letterFiber (gcwCoarseLabelling μ c) CWBlock.zero =
          ({GenCWIndex.zero} : Finset (GenCWIndex μ)) := by
        ext x; cases x <;> simp [gcwCoarseLabelling, gcwBlockLabel]
      simp [Tensor.blockFiberCard, this]
  | last =>
      have : WordType.letterFiber (gcwCoarseLabelling μ c) CWBlock.last =
          ({GenCWIndex.last} : Finset (GenCWIndex μ)) := by
        ext x; cases x <;> simp [gcwCoarseLabelling, gcwBlockLabel]
      simp [Tensor.blockFiberCard, this]
  | middle =>
      have : WordType.letterFiber (gcwCoarseLabelling μ c) CWBlock.middle =
          (Finset.univ : Finset μ).image GenCWIndex.middle := by
        ext x; cases x <;> simp [gcwCoarseLabelling, gcwBlockLabel]
      rw [Tensor.blockFiberCard, this,
        Finset.card_image_of_injective _ (fun a b h ↦ by cases h; rfl)]
      simp

/-- The block `0` is a singleton on every leg. -/
@[simp] theorem blockFiberCard_gcw_zero (c : Leg) :
    Tensor.blockFiberCard (κ := GenCWIndexFamily μ) (gcwCoarseLabelling μ) c CWBlock.zero = 1 := by
  rw [blockFiberCard_gcwCoarseLabelling]; rfl

/-- The middle block has `q` elements on every leg. -/
@[simp] theorem blockFiberCard_gcw_middle (c : Leg) :
    Tensor.blockFiberCard (κ := GenCWIndexFamily μ) (gcwCoarseLabelling μ) c CWBlock.middle =
      Fintype.card μ := by
  rw [blockFiberCard_gcwCoarseLabelling]; rfl

/-- The block `q+1` is a singleton on every leg. -/
@[simp] theorem blockFiberCard_gcw_last (c : Leg) :
    Tensor.blockFiberCard (κ := GenCWIndexFamily μ) (gcwCoarseLabelling μ) c CWBlock.last = 1 := by
  rw [blockFiberCard_gcwCoarseLabelling]; rfl

end Partition

/-! ## Real-analytic lemmas for the three-block value -/

section Analytic

/-- A product over the three legs of legwise geometric terms collects the exponents. -/
private theorem prod_leg_rpow {b₁ b₂ b₃ : ℝ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃)
    (u w z : Leg → ℝ) :
    ∏ c : Leg, (b₁ ^ u c * b₂ ^ w c * b₃ ^ z c) =
      b₁ ^ (∑ c, u c) * b₂ ^ (∑ c, w c) * b₃ ^ (∑ c, z c) := by
  rw [prod_leg, sum_leg, sum_leg, sum_leg, Real.rpow_add hb₁, Real.rpow_add hb₁,
    Real.rpow_add hb₂, Real.rpow_add hb₂, Real.rpow_add hb₃, Real.rpow_add hb₃]
  ring

/-- **The endpoint estimate.**  A product of three geometric terms whose exponents depend affinely
on one parameter `A ∈ [0,1]` is itself geometric in `A`, hence maximal at an endpoint; under the
hypothesis `b₂² ≤ b₁·b₃` the geometric ratio is at least `1` and the maximum is at `A = 1`.

Proof sketch: `b₁^A·b₂^{2−2A}·b₃^{1+A} = (b₂²·b₃)·(b₁·b₃/b₂²)^A` by the `rpow` laws, the ratio
`b₁·b₃/b₂²` is at least `1`, and `x^A ≤ x^1` for `1 ≤ x` and `A ≤ 1`. -/
private theorem rpow_affine_le_of_sq_le {b₁ b₂ b₃ A : ℝ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hb₃ : 0 < b₃) (hA : A ≤ 1) (hratio : b₂ ^ 2 ≤ b₁ * b₃) :
    b₁ ^ A * b₂ ^ (2 - 2 * A) * b₃ ^ (1 + A) ≤ b₁ * b₃ ^ 2 := by
  have hb₂sq : (0 : ℝ) < b₂ ^ 2 := by positivity
  have hrat : 1 ≤ b₁ * b₃ / b₂ ^ 2 := (one_le_div hb₂sq).mpr hratio
  have h2 : b₂ ^ ((2 : ℝ) * A) = (b₂ ^ (2 : ℕ)) ^ A := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast_mul hb₂.le 2 A]
  have h2' : b₂ ^ ((2 : ℝ)) = b₂ ^ (2 : ℕ) := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hkey : b₁ ^ A * b₂ ^ (2 - 2 * A) * b₃ ^ (1 + A) =
      (b₂ ^ 2 * b₃) * (b₁ * b₃ / b₂ ^ 2) ^ A := by
    rw [Real.rpow_sub hb₂, Real.rpow_add hb₃, Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow hb₁.le hb₃.le, h2, h2', Real.rpow_one]
    field_simp
  rw [hkey]
  have hstep : (b₁ * b₃ / b₂ ^ 2) ^ A ≤ (b₁ * b₃ / b₂ ^ 2) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hrat hA
  rw [Real.rpow_one] at hstep
  calc (b₂ ^ 2 * b₃) * (b₁ * b₃ / b₂ ^ 2) ^ A
      ≤ (b₂ ^ 2 * b₃) * (b₁ * b₃ / b₂ ^ 2) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = b₁ * b₃ ^ 2 := by field_simp

/-- If the product of three nonnegative reals is at most `M³` then one of them is at most `M`. -/
private theorem exists_le_of_prod_le_pow {f : Leg → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∏ c, f c ≤ M ^ 3) : ∃ c, f c ≤ M := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  rw [prod_leg] at h
  have h1 : M * M < f Leg.X * f Leg.Y := mul_lt_mul'' (hcon Leg.X) (hcon Leg.Y) hM hM
  have h2 : M * M * M < f Leg.X * f Leg.Y * f Leg.Z :=
    mul_lt_mul'' h1 (hcon Leg.Z) (by positivity) hM
  nlinarith

end Analytic

/-! ## The marginals of a distribution on the six blocks -/

section Marginals

variable (p : ProbabilityVector GcwBlockIndex)

/-- The mass of the block `q+1` in the leg-`c` marginal is the mass of the corner block of that
leg. -/
theorem gcwMarginal_last (c : Leg) :
    (p.pushforward fun j ↦ gcwBlockAddress j c).weight CWBlock.last =
      p.weight (Sum.inl c) := by
  rw [ProbabilityVector.pushforward_weight, Fintype.sum_sum_type]
  cases c <;> simp [gcwBlockAddress, sum_leg]

/-- The mass of the middle block in the leg-`c` marginal is the total middle mass minus the mass of
the block that is `0` on leg `c`. -/
theorem gcwMarginal_middle (c : Leg) :
    (p.pushforward fun j ↦ gcwBlockAddress j c).weight CWBlock.middle =
      (∑ c', p.weight (Sum.inr c')) - p.weight (Sum.inr c) := by
  rw [ProbabilityVector.pushforward_weight, Fintype.sum_sum_type]
  cases c <;> simp [gcwBlockAddress, sum_leg] <;> ring

/-- The mass of the block `0` in the leg-`c` marginal. -/
theorem gcwMarginal_zero (c : Leg) :
    (p.pushforward fun j ↦ gcwBlockAddress j c).weight CWBlock.zero =
      (∑ c', p.weight (Sum.inl c')) - p.weight (Sum.inl c) + p.weight (Sum.inr c) := by
  rw [ProbabilityVector.pushforward_weight, Fintype.sum_sum_type]
  cases c <;> simp [gcwBlockAddress, sum_leg] <;> ring

/-- The corner mass and the middle mass of a distribution on the six blocks add up to `1`. -/
theorem gcwCornerMass_add_middleMass :
    (∑ c, p.weight (Sum.inl c)) + ∑ c, p.weight (Sum.inr c) = 1 := by
  rw [← Fintype.sum_sum_type]
  exact p.total

/-- The corner mass is at most `1`. -/
theorem gcwCornerMass_le_one : (∑ c, p.weight (Sum.inl c)) ≤ 1 := by
  have h := gcwCornerMass_add_middleMass p
  have hmid : 0 ≤ ∑ c, p.weight (Sum.inr c) :=
    Finset.sum_nonneg fun c _ ↦ p.nonneg _
  linarith

end Marginals

/-! ## The block value certificate, shared by every measure

The hypothesis of Alman's Theorem 5.3 --- "for every distribution `p` on the six blocks, some leg
has block value at most `M`" --- mentions neither the coefficient semiring nor the invariant being
bounded.  It is therefore proved once here, and consumed by
`Tensor.asymptoticIndependenceNumber_le_of_blockEntropy` below for `Ī` and by
`Tensor.asymptoticSliceRank_coordinateTensor_le_of_blockEntropy` in
`Examples/GeneralizedCoppersmithWinogradSliceRankUpper.lean` for `S̃`. -/

section BlockValue

variable {μ : Type} [Fintype μ] [DecidableEq μ]

/-- **The reference-vector block value certificate for `CW_q^σ`.**  Let `r` be a probability vector
with positive weights on the three blocks `{0}`, `{1,…,q}`, `{q+1}`.  If

```text
(q / r_middle)² ≤ (1 / r_last) · (1 / r_zero)      and      (1 / r_last) · (1 / r_zero)² ≤ M³,
```

then for every distribution `p` on the six non-zero blocks some leg has block value at most `M`.

Proof sketch.  For a distribution `p` on the six blocks and each leg `c`, Gibbs' inequality against
`r` (`blockLegValue_le_prod_rpow`) gives

```text
p_c ≤ (1/r_last)^{m_c(last)} · (q/r_middle)^{m_c(middle)} · (1/r_zero)^{m_c(zero)},
```

where the block sizes are `1, q, 1` (`blockFiberCard_gcwCoarseLabelling`).  Multiplying over the
three legs collects the exponents into the three totals `A`, `2−2A` and `1+A`, where `A` is the
total corner mass of `p` (`gcwMarginal_last`, `gcwMarginal_middle`, `gcwMarginal_zero`); the
resulting expression is geometric in `A ∈ [0,1]` and, by the first hypothesis, maximal at `A = 1`
(`rpow_affine_le_of_sq_le`), where its value is `(1/r_last)·(1/r_zero)² ≤ M³`.  Since the product of
the three leg values is at most `M³`, one of them is at most `M`. -/
theorem gcwBlockLegValue_le_of_reference (hq : 1 ≤ Fintype.card μ)
    {r : CWBlock → ℝ} (hr : ∀ a, 0 < r a) (hrsum : ∑ a, r a = 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hratio : ((Fintype.card μ : ℝ) / r .middle) ^ 2 ≤ (1 / r .last) * (1 / r .zero))
    (hcube : (1 / r .last) * (1 / r .zero) ^ 2 ≤ M ^ 3)
    (p : ProbabilityVector GcwBlockIndex) :
    ∃ c : Leg, blockLegValue
        (fun a ↦ ((Tensor.blockFiberCard (κ := GenCWIndexFamily μ)
          (gcwCoarseLabelling μ) c a : ℕ) : ℝ))
        ((p.pushforward fun j ↦ gcwBlockAddress j c).weight) ≤ M := by
  classical
  have hqR : (0 : ℝ) < (Fintype.card μ : ℝ) := by exact_mod_cast hq
  set b₁ : ℝ := 1 / r CWBlock.last with hb₁def
  set b₂ : ℝ := (Fintype.card μ : ℝ) / r CWBlock.middle with hb₂def
  set b₃ : ℝ := 1 / r CWBlock.zero with hb₃def
  have hb₁ : 0 < b₁ := one_div_pos.mpr (hr _)
  have hb₂ : 0 < b₂ := div_pos hqR (hr _)
  have hb₃ : 0 < b₃ := one_div_pos.mpr (hr _)
  set m : Leg → CWBlock → ℝ :=
    fun c ↦ (p.pushforward fun j ↦ gcwBlockAddress j c).weight with hmdef
  -- The three marginal totals, in terms of the corner mass `A`.
  set A : ℝ := ∑ c, p.weight (Sum.inl c) with hAdef
  have htot : (p.weight (Sum.inl Leg.X) + p.weight (Sum.inl Leg.Y) + p.weight (Sum.inl Leg.Z)) +
      (p.weight (Sum.inr Leg.X) + p.weight (Sum.inr Leg.Y) + p.weight (Sum.inr Leg.Z)) = 1 := by
    have h := gcwCornerMass_add_middleMass p
    rwa [sum_leg, sum_leg] at h
  have hAexp : A = p.weight (Sum.inl Leg.X) + p.weight (Sum.inl Leg.Y) +
      p.weight (Sum.inl Leg.Z) := by rw [hAdef, sum_leg]
  have hlast : ∑ c, m c CWBlock.last = A := by
    simp only [hmdef, gcwMarginal_last, hAdef]
  have hmiddle : ∑ c, m c CWBlock.middle = 2 - 2 * A := by
    simp only [hmdef, gcwMarginal_middle, sum_leg]
    rw [hAexp]; linarith
  have hzero : ∑ c, m c CWBlock.zero = 1 + A := by
    simp only [hmdef, gcwMarginal_zero, sum_leg]
    rw [hAexp]; linarith
  have hA1 : A ≤ 1 := by
    rw [hAdef]; exact gcwCornerMass_le_one p
  -- The Gibbs bound on each leg.
  have hleg : ∀ c : Leg,
      blockLegValue
          (fun a ↦ ((Tensor.blockFiberCard (κ := GenCWIndexFamily μ)
            (gcwCoarseLabelling μ) c a : ℕ) : ℝ)) (m c) ≤
        b₁ ^ (m c CWBlock.last) * b₂ ^ (m c CWBlock.middle) * b₃ ^ (m c CWBlock.zero) := by
    intro c
    refine le_trans (blockLegValue_le_prod_rpow (fun a ↦ by positivity)
      (fun a ↦ (p.pushforward fun j ↦ gcwBlockAddress j c).nonneg a)
      (p.pushforward fun j ↦ gcwBlockAddress j c).total hr hrsum) ?_
    rw [prod_cwBlock]
    simp only [blockFiberCard_gcw_zero, blockFiberCard_gcw_middle, blockFiberCard_gcw_last,
      Nat.cast_one, hb₁def, hb₂def, hb₃def]
    exact le_of_eq (by ring)
  refine exists_le_of_prod_le_pow hM ?_
  calc ∏ c : Leg, blockLegValue
          (fun a ↦ ((Tensor.blockFiberCard (κ := GenCWIndexFamily μ)
            (gcwCoarseLabelling μ) c a : ℕ) : ℝ)) (m c)
      ≤ ∏ c : Leg, (b₁ ^ (m c CWBlock.last) * b₂ ^ (m c CWBlock.middle) *
          b₃ ^ (m c CWBlock.zero)) :=
        Finset.prod_le_prod
          (fun c _ ↦ blockLegValue_nonneg (fun a ↦ by positivity)
            (fun a ↦ (p.pushforward fun j ↦ gcwBlockAddress j c).nonneg a))
          (fun c _ ↦ hleg c)
    _ = b₁ ^ (∑ c, m c CWBlock.last) * b₂ ^ (∑ c, m c CWBlock.middle) *
          b₃ ^ (∑ c, m c CWBlock.zero) := prod_leg_rpow hb₁ hb₂ hb₃ _ _ _
    _ = b₁ ^ A * b₂ ^ (2 - 2 * A) * b₃ ^ (1 + A) := by rw [hlast, hmiddle, hzero]
    _ ≤ b₁ * b₃ ^ 2 := rpow_affine_le_of_sq_le hb₁ hb₂ hb₃ hA1 hratio
    _ ≤ M ^ 3 := hcube

/-- **The closed-form block value certificate for `CW_q^σ`** [Alman2019, §5.5.1]: for every `q ≥ 1`
and every real `u > 0`, every distribution on the six non-zero blocks has some leg of block value at
most `u^{1/3}·(q + u + 1/u)`.

Proof sketch: instantiate `gcwBlockLegValue_le_of_reference` at the reference vector
`r_zero = 1/(uS)`, `r_middle = q/S`, `r_last = u/S` with `S = q + u + 1/u`, for which the two
hypotheses hold with *equality*: `(q/r_middle)² = S² = (1/r_last)(1/r_zero)` and
`(1/r_last)(1/r_zero)² = u·S³ = (u^{1/3}·S)³`. -/
theorem gcwBlockLegValue_le_rpow_mul (hq : 1 ≤ Fintype.card μ) {u : ℝ} (hu : 0 < u)
    (p : ProbabilityVector GcwBlockIndex) :
    ∃ c : Leg, blockLegValue
        (fun a ↦ ((Tensor.blockFiberCard (κ := GenCWIndexFamily μ)
          (gcwCoarseLabelling μ) c a : ℕ) : ℝ))
        ((p.pushforward fun j ↦ gcwBlockAddress j c).weight) ≤
      u ^ ((3 : ℝ)⁻¹) * ((Fintype.card μ : ℝ) + u + u⁻¹) := by
  have hqR : (0 : ℝ) < (Fintype.card μ : ℝ) := by exact_mod_cast hq
  set S : ℝ := (Fintype.card μ : ℝ) + u + u⁻¹ with hSdef
  have hS : 0 < S := by rw [hSdef]; positivity
  set r : CWBlock → ℝ := fun a ↦
    match a with
    | .zero => 1 / (u * S)
    | .middle => (Fintype.card μ : ℝ) / S
    | .last => u / S with hrdef
  have hr : ∀ a, 0 < r a := by
    intro a
    cases a with
    | zero => exact one_div_pos.mpr (by positivity)
    | middle => exact div_pos hqR hS
    | last => exact div_pos hu hS
  have hcube : (u ^ ((3 : ℝ)⁻¹)) ^ 3 = u := by
    rw [show ((3 : ℝ))⁻¹ = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hu.le (by norm_num)
  refine gcwBlockLegValue_le_of_reference hq hr ?_ (by positivity) (le_of_eq ?_) (le_of_eq ?_) p
  · rw [sum_cwBlock]
    show 1 / (u * S) + (Fintype.card μ : ℝ) / S + u / S = 1
    rw [hSdef]
    field_simp
    ring
  · show ((Fintype.card μ : ℝ) / ((Fintype.card μ : ℝ) / S)) ^ 2 =
      1 / (u / S) * (1 / (1 / (u * S)))
    field_simp
  · rw [mul_pow, hcube]
    show 1 / (u / S) * (1 / (1 / (u * S))) ^ 2 = u * S ^ 3
    field_simp

/-- **The `q = 6` block value certificate**, from the rational parameter `u = (13/20)³ = 2197/8000`,
for which the analytic bound `u^{1/3}(q + u + 1/u)` evaluates to the rational number

```text
(13/20) · (6 + 2197/8000 + 8000/2197) = 174282809/27040000 = 6.4453701…,
```

comfortably below `6.45`.  Alman's exact value is `6.44493…` [Alman2019, p. 71]. -/
theorem gcwBlockLegValue_fin_six_le (p : ProbabilityVector GcwBlockIndex) :
    ∃ c : Leg, blockLegValue
        (fun a ↦ ((Tensor.blockFiberCard (κ := GenCWIndexFamily (Fin 6))
          (gcwCoarseLabelling (Fin 6)) c a : ℕ) : ℝ))
        ((p.pushforward fun j ↦ gcwBlockAddress j c).weight) ≤ 6.45 := by
  have hcard : Fintype.card (Fin 6) = 6 := Fintype.card_fin 6
  have hu : (0 : ℝ) < (13 / 20 : ℝ) ^ (3 : ℕ) := by norm_num
  have hroot : (((13 / 20 : ℝ) ^ (3 : ℕ)) ^ ((3 : ℝ)⁻¹)) = 13 / 20 := by
    rw [show ((3 : ℝ))⁻¹ = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  obtain ⟨c, hc⟩ := gcwBlockLegValue_le_rpow_mul (μ := Fin 6) (by rw [hcard]; norm_num) hu p
  refine ⟨c, hc.trans ?_⟩
  rw [hroot, hcard]
  norm_num

/-- **The `q = 1` block value certificate**, the smallest parameter of Alman's table on p. 71 of
[Alman2019], whose exact value is `2.7551…`.  The certificate is `u = (21/25)³`, for which the
analytic bound evaluates to `474609871/172265625 = 2.7551049…`. -/
theorem gcwBlockLegValue_fin_one_le (p : ProbabilityVector GcwBlockIndex) :
    ∃ c : Leg, blockLegValue
        (fun a ↦ ((Tensor.blockFiberCard (κ := GenCWIndexFamily (Fin 1))
          (gcwCoarseLabelling (Fin 1)) c a : ℕ) : ℝ))
        ((p.pushforward fun j ↦ gcwBlockAddress j c).weight) ≤ 2.7552 := by
  have hcard : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1
  have hu : (0 : ℝ) < (21 / 25 : ℝ) ^ (3 : ℕ) := by norm_num
  have hroot : (((21 / 25 : ℝ) ^ (3 : ℕ)) ^ ((3 : ℝ)⁻¹)) = 21 / 25 := by
    rw [show ((3 : ℝ))⁻¹ = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  obtain ⟨c, hc⟩ := gcwBlockLegValue_le_rpow_mul (μ := Fin 1) (by rw [hcard]) hu p
  refine ⟨c, hc.trans ?_⟩
  rw [hroot, hcard]
  norm_num

end BlockValue

/-! ## The block-entropy bound on `Ī(CW_q^σ)` -/

section Upper

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
variable {μ : Type} [Fintype μ] [DecidableEq μ]

/-- **Alman's Theorem 5.3 on `CW_q^σ`, in reference-vector form.**  Let `r` be a probability vector
with positive weights on the three blocks `{0}`, `{1,…,q}`, `{q+1}`.  If

```text
(q / r_middle)² ≤ (1 / r_last) · (1 / r_zero)      and      (1 / r_last) · (1 / r_zero)² ≤ M³,
```

then `Ī(CW_q^σ) ≤ M`.

Proof sketch.  Apply `Tensor.asymptoticIndependenceNumber_le_of_blockEntropy` with the six-block
cover `gcwTable_blockCover`.  For a distribution `p` on the six blocks and each leg `c`, Gibbs'
inequality against `r` (`blockLegValue_le_prod_rpow`) gives

```text
p_c ≤ (1/r_last)^{m_c(last)} · (q/r_middle)^{m_c(middle)} · (1/r_zero)^{m_c(zero)},
```

where the block sizes are `1, q, 1` (`blockFiberCard_gcwCoarseLabelling`).  Multiplying over the
three legs collects the exponents into the three totals `A`, `2−2A` and `1+A`, where `A` is the
total corner mass of `p` (`gcwMarginal_last`, `gcwMarginal_middle`, `gcwMarginal_zero`); the
resulting expression is geometric in `A ∈ [0,1]` and, by the first hypothesis, maximal at `A = 1`
(`rpow_affine_le_of_sq_le`), where its value is `(1/r_last)·(1/r_zero)² ≤ M³`.  Since the product of
the three leg values is at most `M³`, one of them is at most `M`. -/
theorem asymptoticIndependenceNumber_gcwTable_le_of_reference (σ : Equiv.Perm μ)
    (hq : 1 ≤ Fintype.card μ) {r : CWBlock → ℝ} (hr : ∀ a, 0 < r a) (hrsum : ∑ a, r a = 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hratio : ((Fintype.card μ : ℝ) / r .middle) ^ 2 ≤ (1 / r .last) * (1 / r .zero))
    (hcube : (1 / r .last) * (1 / r .zero) ^ 2 ≤ M ^ 3) :
    asymptoticIndependenceNumber (gcwTable K μ σ) ≤ M :=
  Tensor.asymptoticIndependenceNumber_le_of_blockEntropy
    (blk := gcwCoarseLabelling μ) (β := gcwBlockAddress)
    (fun s hs ↦ gcwTable_blockCover (K := K) σ s hs) hM
    (gcwBlockLegValue_le_of_reference hq hr hrsum hM hratio hcube)

/-- **The closed-form block-entropy bound on `Ī(CW_q^σ)`** [Alman2019, §5.5.1].  For every
parameter `q ≥ 1`, every middle permutation `σ` and every real `u > 0`,

```text
Ī(CW_q^σ) ≤ u^{1/3} · (q + u + 1/u).
```

The infimum of the right-hand side over `u > 0` is exactly Alman's

```text
sup_{v ∈ [0,1/3]} q^{2(1/3−v)} / (v^v (2/3−2v)^{2/3−2v} (1/3+v)^{1/3+v}),
```

the two being Legendre-dual descriptions of the same number: the optimal `u` is the root of
`4u² + qu − 2 = 0` after the substitution that makes the reference vector proportional to the
optimal marginal.  Numerically the optimum is `2.7551…` at `q = 1` and `6.44493…` at `q = 6`,
reproducing the table on p. 71 of [Alman2019].

Proof sketch: instantiate `asymptoticIndependenceNumber_gcwTable_le_of_reference` at the
reference vector `r_zero = 1/(uS)`, `r_middle = q/S`, `r_last = u/S` with `S = q + u + 1/u`, for
which the two hypotheses hold with *equality*: `(q/r_middle)² = S² = (1/r_last)(1/r_zero)` and
`(1/r_last)(1/r_zero)² = u·S³ = (u^{1/3}·S)³`. -/
theorem asymptoticIndependenceNumber_gcwTable_le_rpow_mul (σ : Equiv.Perm μ)
    (hq : 1 ≤ Fintype.card μ) {u : ℝ} (hu : 0 < u) :
    asymptoticIndependenceNumber (gcwTable K μ σ) ≤
      u ^ ((3 : ℝ)⁻¹) * ((Fintype.card μ : ℝ) + u + u⁻¹) :=
  Tensor.asymptoticIndependenceNumber_le_of_blockEntropy
    (blk := gcwCoarseLabelling μ) (β := gcwBlockAddress)
    (fun s hs ↦ gcwTable_blockCover (K := K) σ s hs)
    (by
      have : (0 : ℝ) < (Fintype.card μ : ℝ) := by exact_mod_cast hq
      positivity)
    (gcwBlockLegValue_le_rpow_mul hq hu)

/-! ## The numerical instances -/

/-- **`Ī(CW_6^σ) ≤ 6.45`** for every permutation `σ` of the six middle coordinates, on the literal
index set of [AlmanVassilevskaWilliams2018, Definition 3.1].

The certificate is the rational parameter `u = (13/20)³ = 2197/8000`, for which the analytic bound
`u^{1/3}(q + u + 1/u)` evaluates to the rational number

```text
(13/20) · (6 + 2197/8000 + 8000/2197) = 174282809/27040000 = 6.4453701…,
```

comfortably below `6.45`.  Alman's exact value is `S̃(CW_{6,σ}) = 6.44493…` [Alman2019, p. 71]. -/
theorem asymptoticIndependenceNumber_gcwTable_fin_six_le (σ : Equiv.Perm (Fin 6)) :
    asymptoticIndependenceNumber (gcwTable K (Fin 6) σ) ≤ 6.45 :=
  Tensor.asymptoticIndependenceNumber_le_of_blockEntropy
    (blk := gcwCoarseLabelling (Fin 6)) (β := gcwBlockAddress)
    (fun s hs ↦ gcwTable_blockCover (K := K) σ s hs) (by norm_num)
    gcwBlockLegValue_fin_six_le

/-- **`Ī(CW_1^σ) ≤ 2.7552`**, the smallest parameter of Alman's table on p. 71 of [Alman2019],
whose exact value is `S̃(CW_{1,σ}) = 2.7551…`.  The certificate is `u = (21/25)³`, for which the
analytic bound evaluates to `474609871/172265625 = 2.7551049…`.

This instance matters for the barrier: the exponent `s = log_{q+2} Ī(CW_q^σ)` in AVW Corollary 4.3
is *largest* at `q = 1`, so the smallest parameters are the binding ones for a bound uniform in
`q`. -/
theorem asymptoticIndependenceNumber_gcwTable_fin_one_le (σ : Equiv.Perm (Fin 1)) :
    asymptoticIndependenceNumber (gcwTable K (Fin 1) σ) ≤ 2.7552 :=
  Tensor.asymptoticIndependenceNumber_le_of_blockEntropy
    (blk := gcwCoarseLabelling (Fin 1)) (β := gcwBlockAddress)
    (fun s hs ↦ gcwTable_blockCover (K := K) σ s hs) (by norm_num)
    gcwBlockLegValue_fin_one_le

/-- **The sharpened numeric sandwich at `q = 6`**, on the literal index set of
[AlmanVassilevskaWilliams2018, Definition 3.1] and for every permutation `σ` of `{1,…,6}`:

```text
6.24 ≤ Ī(CW_6^σ) ≤ 6.45.
```

The lower bound is `avw_gcwTable_independence_sandwich_fin_six`; the upper bound replaces that
statement's `Ī(CW_6^σ) < 8` by the block-entropy bound of [Alman2019, §5.5.1], whose exact value is
`6.44493…`.  Alman's Theorem 5.6 shows that no better upper bound is available from the
slice-rank/independence route, so the remaining gap `[6.24, 6.4449]` can only be closed from
below. -/
theorem avw_gcwTable_independence_sandwich_upper_fin_six (σ : Equiv.Perm (Fin 6)) :
    (6 : ℝ) + 6 / 25 ≤ asymptoticIndependenceNumber (gcwTable K (Fin 6) σ) ∧
      asymptoticIndependenceNumber (gcwTable K (Fin 6) σ) ≤ 6.45 :=
  ⟨(avw_gcwTable_independence_sandwich_fin_six K σ).1,
    asymptoticIndependenceNumber_gcwTable_fin_six_le σ⟩

end Upper

/-! ## The barrier consequence -/

section Barrier

variable {K : Type u} [Field K]

/-- **`6.45 ≤ 8^{26/29}`**, the exponent certificate feeding AVW Corollary 4.3.  In exact rational
arithmetic this is `(129/20)^29 ≤ 8^26`, i.e.
`16110224730539585180469926957611731383378656895721646439370369 ≤ 2^136 · 5^29`. -/
theorem gcw_six_le_rpow_eight : (6.45 : ℝ) ≤ (8 : ℝ) ^ ((26 : ℝ) / 29) := by
  have hpow : ((8 : ℝ) ^ ((26 : ℝ) / 29)) ^ (29 : ℕ) = (8 : ℝ) ^ (26 : ℕ) := by
    rw [← Real.rpow_natCast ((8 : ℝ) ^ ((26 : ℝ) / 29)) 29,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8),
      show ((26 : ℝ) / 29) * ((29 : ℕ) : ℝ) = ((26 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine le_of_pow_le_pow_left₀ (n := 29) (by norm_num) (Real.rpow_nonneg (by norm_num) _) ?_
  rw [hpow]
  norm_num

/-- **The Corollary-4.3 shape for `CW_6^σ` from the block-entropy bound**:
`Ī(CW_6^σ) ≤ R̃(CW_6^σ)^{26/29}` with `26/29 = 0.8965… < 1`.

Proof sketch: `Ī(CW_6^σ) ≤ 6.45 ≤ 8^{26/29} ≤ R̃(CW_6^σ)^{26/29}`, the last step because
`8 = q + 2 ≤ R̃(CW_6^σ)` by conciseness (`card_le_asymptoticRank_gcwTable`). -/
theorem asymptoticIndependenceNumber_gcwTable_fin_six_le_rpow_asymptoticRank
    (σ : Equiv.Perm (Fin 6)) :
    asymptoticIndependenceNumber (gcwTable K (Fin 6) σ) ≤
      Tensor.asymptoticRank (coordinateTensor (gcwTable K (Fin 6) σ)) ^ ((26 : ℝ) / 29) := by
  have hcard := card_le_asymptoticRank_gcwTable (K := K) σ
  rw [Fintype.card_fin] at hcard
  refine le_trans (asymptoticIndependenceNumber_gcwTable_fin_six_le σ) ?_
  exact le_trans gcw_six_le_rpow_eight
    (Real.rpow_le_rpow (by norm_num) (by norm_num at hcard ⊢; linarith) (by norm_num))

/-- **The improved Galactic barrier for `CW_6^σ`.**  For every field `K` and every permutation `σ`
of the six middle coordinates, the Galactic method applied to `CW_6^σ` in its own variables cannot
prove any exponent bound below

```text
6 / (26/29 + 2) = 29/14 = 2.0714…
```

This replaces the constant `60000/29999 = 2.00006…` of
`six_div_le_coordinateGalacticExponent_gcwTable_of_six_le`, which came from the much weaker
`Ī(CW_6^σ) < 8`.  The improvement is exactly the difference between AVW's Lemma 7.2 splitting
argument and Alman's block-entropy bound `Ī(CW_6^σ) ≤ 6.4449…` [Alman2019, §5.5.1].

Proof sketch: AVW Corollary 4.3
(`six_div_add_two_le_coordinateGalacticExponent_of_concise`) applied with `s = 26/29`, using the
conciseness of `gcwTable` (`isCoordinateConcise_gcwTable`), the asymptotic-rank lower bound
`8 ≤ R̃` (`card_le_asymptoticRank_gcwTable`), the Corollary-4.3 shape proved just above, and the
Galactic certificate of `coordinateGalacticValues_gcwTable_nonempty`. -/
theorem coordinateGalacticExponent_gcwTable_fin_six_ge (K : Type u) [Field K]
    (σ : Equiv.Perm (Fin 6)) :
    (29 : ℝ) / 14 ≤ coordinateGalacticExponent K (gcwTable K (Fin 6) σ) := by
  have hconc : ∀ i, Tensor.IsCoordinateConcise (gcwTable K (Fin 6) σ) i :=
    fun i ↦ isCoordinateConcise_gcwTable K σ i
  have hcard := card_le_asymptoticRank_gcwTable (K := K) σ
  rw [Fintype.card_fin] at hcard
  have hR : 1 < Tensor.asymptoticRank (coordinateTensor (gcwTable K (Fin 6) σ)) := by
    norm_num at hcard; linarith
  have hmain := six_div_add_two_le_coordinateGalacticExponent_of_concise K
    (s := (26 : ℝ) / 29) hconc hR (by norm_num)
    (asymptoticIndependenceNumber_gcwTable_fin_six_le_rpow_asymptoticRank σ)
    (coordinateGalacticValues_gcwTable_nonempty K σ)
  rwa [show (6 : ℝ) / ((26 : ℝ) / 29 + 2) = 29 / 14 by norm_num] at hmain

/-- **The Galactic exponent of `CW_6^σ` is strictly above `2`, by the margin `1/14`.** -/
theorem two_lt_coordinateGalacticExponent_gcwTable_fin_six (K : Type u) [Field K]
    (σ : Equiv.Perm (Fin 6)) :
    2 < coordinateGalacticExponent K (gcwTable K (Fin 6) σ) :=
  lt_of_lt_of_le (by norm_num) (coordinateGalacticExponent_gcwTable_fin_six_ge K σ)

end Barrier

end AlgebraicComplexity.Examples
