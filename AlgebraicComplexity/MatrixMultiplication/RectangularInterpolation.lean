/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RectangularExponent
import Mathlib.Analysis.Convex.Function

/-!
# Interpolation and convexity for the rectangular exponent

This module proves the first substantive laws of the rectangular matrix-multiplication exponent
`ω(κ) = rectangularOmega K κ` defined in `MatrixMultiplication/RectangularExponent.lean`: the
external-product *splitting* law, its two headline consequences — the interpolation upper bound
`ω(κ) ≤ κ·ω + 2·(1 - κ)` on `0 ≤ κ ≤ 1` and convexity of `κ ↦ ω(κ)` on `[0, ∞)` — and the
`κ ≥ 1` blocking law `ω(κ) ≤ ω + (κ - 1)`.

## Principal results

* `rectangularMatrixRankSequence_le_mul_split`: the finite splitting inequality
  `rank ⟨n, ⌈n^(θκ₁ + (1-θ)κ₂)⌉, n⟩ ≤ rank ⟨n₁, ⌈n₁^κ₁⌉, n₁⟩ · rank ⟨n₂, ⌈n₂^κ₂⌉, n₂⟩`
  with `n₁ = ⌈n^θ⌉` and `n₂ = ⌈n^(1-θ)⌉`, over every commutative semiring;
* `rectangularMatrixExponentLE_split`: the same split at the level of admissible polynomial
  exponents, `τ ↦ θτ₁ + (1-θ)τ₂`;
* `rectangularOmega_split_le` / `rectangularOmega_convexOn`: convexity of `κ ↦ ω(κ)` on
  `[0, ∞)`, i.e. `ω(θκ₁ + (1-θ)κ₂) ≤ θ·ω(κ₁) + (1-θ)·ω(κ₂)` for `0 ≤ θ ≤ 1`, over every
  commutative semiring, packaged also as a Mathlib `ConvexOn ℝ (Set.Ici 0)` statement;
* `rectangularOmega_le_interpolation`: the interpolation bound `ω(κ) ≤ κ·ω + 2·(1 - κ)` for
  `0 ≤ κ ≤ 1`, obtained from the split at `(κ₁, κ₂, θ) = (1, 0, κ)`;
* `rectangularOmega_le_omega_add_sub_one`: the blocking bound `ω(κ) ≤ ω + (κ - 1)` for `κ ≥ 1`;
* `rectangularOmega_le_interpolation_of_eq_two`: the Lotti–Romani interpolation formula
  `ω(κ) ≤ 2 + (ω - 2)·(κ - κ₀)/(1 - κ₀)` for `κ₀ ≤ κ ≤ 1` whenever `ω(κ₀) = 2`;
* `rectangularOmega_rectangularAlpha`: over a field the supremum defining the dual exponent is
  **attained**, `ω(α) = 2`.  Together with `rectangularOmega_eq_two_of_lt_rectangularAlpha`
  (proved upstream in `RectangularExponent.lean`) this identifies `[0, α]` as a closed interval
  of optimality, and it removes the arbitrary witness from the classical statement:
  `rectangularOmega_le_interpolation_rectangularAlpha` is the Lotti–Romani formula at `κ₀ = α`
  itself;
* `omega_eq_two_of_rectangularAlpha_eq_one` and `rectangularAlpha_eq_one_iff_omega_eq_two`: over
  a field, `α = 1` if and only if `ω = 2`.  The forward direction is the converse that
  `RectangularExponent.lean` deliberately left open for want of a regularity statement about
  `κ ↦ ω(κ)`; convexity plus the blocking law supplies exactly that regularity.

## Layer placement and strategy

This is a leaf module of the matrix-multiplication theory layer (layer 3), immediately downstream
of `MatrixMultiplication/RectangularExponent.lean` and using nothing from the paper clients.  Its
only new Mathlib dependency beyond that module is `Mathlib.Analysis.Convex.Function`, needed for
the packaged `ConvexOn` statement.

Everything rests on one construction, the rectangular external product law
`Tensor.RankLE.matrixMultiplication_mul` of `AlgebraicComplexity/MatrixMultiplication.lean`:

```text
⟨n₁, n₁^κ₁, n₁⟩ ⊗ ⟨n₂, n₂^κ₂, n₂⟩ = ⟨n₁n₂, n₁^κ₁·n₂^κ₂, n₁n₂⟩.
```

Taking `n₁ ≈ n^θ` and `n₂ ≈ n^(1-θ)` makes the outer dimensions multiply to `n` and the middle
dimension to `n^(θκ₁ + (1-θ)κ₂)`, which is the whole content of both interpolation and convexity.
The interpolation bound is the case `(κ₁, κ₂, θ) = (1, 0, κ)`: the split is then
`⟨n, ⌈n^κ⌉, n⟩ ⪯ ⟨⌈n^κ⌉, ⌈n^κ⌉, ⌈n^κ⌉⟩ ⊗ ⟨⌈n^(1-κ)⌉, 1, ⌈n^(1-κ)⌉⟩`, where the first factor is
handled by any square algorithm and the second factor is an outer product of rank `⌈n^(1-κ)⌉²`.

### Ceiling bookkeeping

`rectangularMiddleDimension κ n = ⌈(n : ℝ)^κ⌉₊` is a ceiling, so none of the three dimensions
matches its ideal real value exactly.  Two observations keep this harmless, and they are isolated
as separate lemmas — the *downwards* one next to the definition it is about, in
`RectangularExponent.lean` — so that the analytic estimates never mention `Nat.ceil` again:

* *upwards*: the required dimension inequalities are all of the form `⌈x⌉₊ ≤ N` with `N` a
  natural number already built from ceilings, so `Nat.ceil_le` reduces them to the real
  inequality `x ≤ N`, and `Nat.le_ceil` provides `n^θ ≤ n₁`, `n^(1-θ) ≤ n₂` on the nose.  No
  rounding loss at all is incurred here: `n ≤ n₁·n₂` and `⌈n^(θκ₁+(1-θ)κ₂)⌉ ≤ ⌈n₁^κ₁⌉·⌈n₂^κ₂⌉`
  are exact (`le_mul_rectangularMiddleDimension_of_split`,
  `rectangularMiddleDimension_le_mul_of_split`);
* *downwards*: rounding up costs at most a factor two, `⌈n^κ⌉ ≤ 2·n^κ` for `κ ≥ 0` and `n ≥ 1`
  (`rectangularMiddleDimension_le_two_mul_rpow`), because `n^κ ≥ 1` in that range.  A factor
  `2^τ` per factor is absorbed into the constant `C` of `Growth.PolynomialBound`, exactly as
  `rectangularMatrixExponentLE_two_add_max` already absorbs one ceiling.

Since `PolynomialBound` quantifies over a multiplicative constant, both effects are invisible in
the exponent; this is why the theorems below have no error terms.

### From admissible exponents to the infimum

`rectangularOmega` is an infimum, so the split must be transferred through it.  The pattern,
copied from `matrixExponentLE_of_omega_lt` in `MatrixMultiplication/Exponent.lean`, is:
`rectangularMatrixExponentLE_of_rectangularOmega_lt` shows every real strictly above `ω(κ)` is
admissible, the split is applied to `ω(κᵢ) + ε/2`, and `le_of_forall_pos_le_add` removes `ε`.

## Non-goals

* Coppersmith's `α > 0` is not proved here; it needs a genuine rectangular construction, and is
  proved in `Examples/CoppersmithRectangular1982.lean`
  (`coppersmith1982_rectangularAlpha_ge`: `2 * log 2 / (5 * log 5) ≤ rectangularAlpha F`, so
  `17/100 < α`).  Until that client existed, everything in this file was vacuously consistent
  with `α = 0`; the interpolation bounds at `κ₀ = rectangularAlpha` are now substantive.
* Only the two-point split is formalized here.  The general `ω(a, b, c)` three-parameter exponent
  is no longer a non-goal: it is `generalRectangularOmega` of
  `MatrixMultiplication/RectangularExponentThree.lean`, where the symmetry, homogeneity and
  information lower bound of Huang–Pan §2 and the two branches of their Theorem 8.1 are proved,
  and where `rectangularOmegaThree K 1 r = rectangularOmega K r` and
  `rectangularOmegaThree K t 1 = rectangularOmega K t` identify this file's exponent as the two
  axes of that one.  The sharper Lotti–Romani estimates that use a rectangular algorithm as one of
  the two factors are still left to a later module.
* The interpolation bound is an upper bound only.  No matching lower bound on `ω(κ)` beyond the
  flattening bound `max 2 (1 + κ)` already in `RectangularExponent.lean` is claimed, and none is
  expected to be easy.

## References

* G. Lotti and F. Romani, *On the asymptotic complexity of rectangular matrix multiplication*,
  Theoretical Computer Science 23 (1983), pp. 171–185.  Section 2 contains the interpolation
  bound `ω(1, κ, 1) ≤ κ·ω + 2(1 - κ)` and the convexity of the exponent function, in the
  equivalent formulation via the exponent `ω(α, β, γ)` of `n^α × n^β` by `n^β × n^γ` products.
* D. Coppersmith, *Rapid multiplication of rectangular matrices*, SIAM J. Comput. 11 (1982),
  pp. 467–471.  The motivating landmark: `α > 0.172`, i.e. `ω(1, κ, 1) = 2` for some `κ > 0`.
  Only its interface with the present file — the conditional corollaries under a hypothesis
  `ω(κ₀) = 2` — is formalized here.
* V. Strassen, *Relative bilinear complexity and matrix multiplication*, J. Reine Angew. Math.
  375/376 (1987), for the modern formulation of the exponent as an infimum over admissible
  polynomial bounds, which is the definition used in `RectangularExponent.lean`.
-/

namespace AlgebraicComplexity

open Tensor Growth

universe u

/-! ## Ceiling bookkeeping for the middle dimension

The two lemmas of this section are the only places in this module where `Nat.ceil` is unfolded,
and both are exact (no rounding loss).  The one place that pays the factor of two absorbed by the
polynomial-bound constant, `rectangularMiddleDimension_le_two_mul_rpow`, lives next to the
definition of `rectangularMiddleDimension` in `RectangularExponent.lean`. -/

/-- The outer dimensions of the split multiply to at least `n`: `n ≤ ⌈n^θ⌉·⌈n^(1-θ)⌉`, with no
rounding loss, for every `n ≥ 1` and every real `θ`.

Proof sketch: `n = n^θ · n^(1-θ)` by `Real.rpow_add`, and each factor is at most its own ceiling
by `Nat.le_ceil`. -/
theorem le_mul_rectangularMiddleDimension_of_split (θ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    n ≤ rectangularMiddleDimension θ n * rectangularMiddleDimension (1 - θ) n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  have hreal : (n : ℝ) ≤
      ((rectangularMiddleDimension θ n * rectangularMiddleDimension (1 - θ) n : ℕ) : ℝ) := by
    have h1 := rpow_le_rectangularMiddleDimension θ n
    have h2 := rpow_le_rectangularMiddleDimension (1 - θ) n
    have hsplit : (n : ℝ) = (n : ℝ) ^ θ * (n : ℝ) ^ (1 - θ) := by
      rw [← Real.rpow_add hnpos]
      norm_num
    rw [hsplit]
    push_cast
    exact mul_le_mul h1 h2 (Real.rpow_nonneg hnpos.le _) (Nat.cast_nonneg _)
  exact_mod_cast hreal

/-- The middle dimensions of the split multiply to at least the required one, with no rounding
loss:
`⌈n^(θκ₁ + (1-θ)κ₂)⌉ ≤ ⌈⌈n^θ⌉^κ₁⌉ · ⌈⌈n^(1-θ)⌉^κ₂⌉` for `0 ≤ κ₁` and `0 ≤ κ₂`.  No hypothesis on
`θ` is needed: the weight only has to be the same on both sides.

Proof sketch: the right-hand side is a natural number, so `Nat.ceil_le` reduces the claim to the
real inequality `n^(θκ₁) · n^((1-θ)κ₂) ≤ ⌈⌈n^θ⌉^κ₁⌉ · ⌈⌈n^(1-θ)⌉^κ₂⌉`.  Each factor is handled
separately: `n^(θκ₁) = (n^θ)^κ₁ ≤ ⌈n^θ⌉^κ₁` by monotonicity of `x ↦ x^κ₁` for `κ₁ ≥ 0`, and then
`Nat.le_ceil`.  Nonnegativity of `κ₁` and `κ₂` is exactly what makes the two monotonicity steps
legal. -/
theorem rectangularMiddleDimension_le_mul_of_split
    {κ₁ κ₂ θ : ℝ} (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    {n : ℕ} (hn : 1 ≤ n) :
    rectangularMiddleDimension (θ * κ₁ + (1 - θ) * κ₂) n ≤
      rectangularMiddleDimension κ₁ (rectangularMiddleDimension θ n) *
        rectangularMiddleDimension κ₂ (rectangularMiddleDimension (1 - θ) n) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  have hA : (n : ℝ) ^ (θ * κ₁) ≤
      (rectangularMiddleDimension κ₁ (rectangularMiddleDimension θ n) : ℝ) := by
    calc
      (n : ℝ) ^ (θ * κ₁) = ((n : ℝ) ^ θ) ^ κ₁ := Real.rpow_mul hnpos.le θ κ₁
      _ ≤ ((rectangularMiddleDimension θ n : ℕ) : ℝ) ^ κ₁ :=
        Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le θ)
          (rpow_le_rectangularMiddleDimension θ n) hκ₁
      _ ≤ _ := rpow_le_rectangularMiddleDimension κ₁ _
  have hB : (n : ℝ) ^ ((1 - θ) * κ₂) ≤
      (rectangularMiddleDimension κ₂ (rectangularMiddleDimension (1 - θ) n) : ℝ) := by
    calc
      (n : ℝ) ^ ((1 - θ) * κ₂) = ((n : ℝ) ^ (1 - θ)) ^ κ₂ := Real.rpow_mul hnpos.le _ κ₂
      _ ≤ ((rectangularMiddleDimension (1 - θ) n : ℕ) : ℝ) ^ κ₂ :=
        Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le _)
          (rpow_le_rectangularMiddleDimension (1 - θ) n) hκ₂
      _ ≤ _ := rpow_le_rectangularMiddleDimension κ₂ _
  apply Nat.ceil_le.mpr
  calc
    (n : ℝ) ^ (θ * κ₁ + (1 - θ) * κ₂)
        = (n : ℝ) ^ (θ * κ₁) * (n : ℝ) ^ ((1 - θ) * κ₂) := Real.rpow_add hnpos _ _
    _ ≤ (rectangularMiddleDimension κ₁ (rectangularMiddleDimension θ n) : ℝ) *
          (rectangularMiddleDimension κ₂ (rectangularMiddleDimension (1 - θ) n) : ℝ) :=
      mul_le_mul hA hB (Real.rpow_nonneg hnpos.le _) (Nat.cast_nonneg _)
    _ = _ := by push_cast; ring

/-- The blocking form of the ceiling bookkeeping: for `κ ≥ 1` and `n ≥ 1`, splitting off one
square factor of side `n` leaves `⌈n^κ⌉ ≤ n · ⌈n^(κ-1)⌉`, with no rounding loss.

Proof sketch: the right-hand side is a natural number, and `n^κ = n · n^(κ-1) ≤ n · ⌈n^(κ-1)⌉`,
so `Nat.ceil_le` applies. -/
theorem rectangularMiddleDimension_le_mul_of_block (κ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    rectangularMiddleDimension κ n ≤ n * rectangularMiddleDimension (κ - 1) n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  apply Nat.ceil_le.mpr
  have hsplit : (n : ℝ) ^ κ = (n : ℝ) * (n : ℝ) ^ (κ - 1) := by
    have hadd := Real.rpow_add hnpos 1 (κ - 1)
    rw [Real.rpow_one] at hadd
    rw [show (1 : ℝ) + (κ - 1) = κ by ring] at hadd
    exact hadd
  calc
    (n : ℝ) ^ κ = (n : ℝ) * (n : ℝ) ^ (κ - 1) := hsplit
    _ ≤ (n : ℝ) * (rectangularMiddleDimension (κ - 1) n : ℝ) :=
      mul_le_mul_of_nonneg_left (rpow_le_rectangularMiddleDimension (κ - 1) n) hnpos.le
    _ = ((n * rectangularMiddleDimension (κ - 1) n : ℕ) : ℝ) := by push_cast; ring

variable (K : Type u) [CommSemiring K]

/-! ## The external-product split at the level of rank sequences -/

/-- **Splitting law for rectangular ranks.**  For `0 ≤ κ₁`, `0 ≤ κ₂` and `n ≥ 1`,

`rank ⟨n, ⌈n^(θκ₁+(1-θ)κ₂)⌉, n⟩ ≤ rank ⟨n₁, ⌈n₁^κ₁⌉, n₁⟩ · rank ⟨n₂, ⌈n₂^κ₂⌉, n₂⟩`

where `n₁ = ⌈n^θ⌉` and `n₂ = ⌈n^(1-θ)⌉`.  This holds over every commutative semiring, and for
every real weight `θ`: the finite construction never needs `0 ≤ θ ≤ 1`, which enters only in the
analytic step `rectangularMatrixExponentLE_split`, where `⌈n^θ⌉ ≤ 2·n^θ` is used.

Proof sketch: the rectangular external-product law
`Tensor.RankLE.matrixMultiplication_mul` multiplies a rank-`r₁` decomposition of
`⟨n₁, ⌈n₁^κ₁⌉, n₁⟩` and a rank-`r₂` decomposition of `⟨n₂, ⌈n₂^κ₂⌉, n₂⟩` into a rank-`r₁r₂`
decomposition of `⟨n₁n₂, ⌈n₁^κ₁⌉·⌈n₂^κ₂⌉, n₁n₂⟩`.  The two ceiling lemmas
`le_mul_rectangularMiddleDimension_of_split` and `rectangularMiddleDimension_le_mul_of_split`
say precisely that the target `⟨n, ⌈n^(θκ₁+(1-θ)κ₂)⌉, n⟩` fits inside that product tensor in all
three dimensions, so `matrixMultiplication_restricts` transports the certificate. -/
theorem rectangularMatrixRankSequence_le_mul_split
    {κ₁ κ₂ θ : ℝ} (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    {n : ℕ} (hn : 1 ≤ n) :
    rectangularMatrixRankSequence K (θ * κ₁ + (1 - θ) * κ₂) n ≤
      rectangularMatrixRankSequence K κ₁ (rectangularMiddleDimension θ n) *
        rectangularMatrixRankSequence K κ₂ (rectangularMiddleDimension (1 - θ) n) := by
  have houter : n ≤ rectangularMiddleDimension θ n * rectangularMiddleDimension (1 - θ) n :=
    le_mul_rectangularMiddleDimension_of_split θ hn
  have hmid := rectangularMiddleDimension_le_mul_of_split (θ := θ) hκ₁ hκ₂ hn
  have h₁ : RankLE (rectangularMatrixRankSequence K κ₁ (rectangularMiddleDimension θ n))
      (matrixMultiplication (K := K) (rectangularMiddleDimension θ n)
        (rectangularMiddleDimension κ₁ (rectangularMiddleDimension θ n))
        (rectangularMiddleDimension θ n)) :=
    rank_spec _
  have h₂ : RankLE (rectangularMatrixRankSequence K κ₂ (rectangularMiddleDimension (1 - θ) n))
      (matrixMultiplication (K := K) (rectangularMiddleDimension (1 - θ) n)
        (rectangularMiddleDimension κ₂ (rectangularMiddleDimension (1 - θ) n))
        (rectangularMiddleDimension (1 - θ) n)) :=
    rank_spec _
  exact rank_le_iff.mpr
    ((h₁.matrixMultiplication_mul h₂).of_restricts
      (matrixMultiplication_restricts (K := K) houter hmid houter))

/-- **Blocking law for rectangular ranks.**  For `κ ≥ 1` and `n ≥ 1`,

`rank ⟨n, ⌈n^κ⌉, n⟩ ≤ rank ⟨n, n, n⟩ · ⌈n^(κ-1)⌉`,

over every commutative semiring: an `n × n^κ` by `n^κ × n` product is a row of `n^(κ-1)`
independent `n × n` by `n × n` products, added together.

Proof sketch: the external product of `⟨n,n,n⟩` with the trivial tensor `⟨1, b, 1⟩`, `b =
⌈n^(κ-1)⌉`, is `⟨n, n·b, n⟩`; the second factor has the elementary rank bound `1·b·1 = b`.  The
ceiling lemma `rectangularMiddleDimension_le_mul_of_block` gives `⌈n^κ⌉ ≤ n·b`, so
`matrixMultiplication_restricts` transports the product certificate to `⟨n, ⌈n^κ⌉, n⟩`. -/
theorem rectangularMatrixRankSequence_le_mul_block
    (κ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    rectangularMatrixRankSequence K κ n ≤
      squareMatrixRankSequence K n * rectangularMiddleDimension (κ - 1) n := by
  have hmid := rectangularMiddleDimension_le_mul_of_block κ hn
  have h₁ : RankLE (squareMatrixRankSequence K n)
      (matrixMultiplication (K := K) n n n) := rank_spec _
  have h₂ : RankLE (1 * rectangularMiddleDimension (κ - 1) n * 1)
      (matrixMultiplication (K := K) 1 (rectangularMiddleDimension (κ - 1) n) 1) :=
    matrixMultiplication_rankLE (K := K) 1 (rectangularMiddleDimension (κ - 1) n) 1
  have h₃ := h₁.matrixMultiplication_mul h₂
  have houter : n ≤ n * 1 := by omega
  have h₄ := h₃.of_restricts
    (matrixMultiplication_restricts (K := K) houter hmid houter)
  have hcount : squareMatrixRankSequence K n *
      (1 * rectangularMiddleDimension (κ - 1) n * 1) =
      squareMatrixRankSequence K n * rectangularMiddleDimension (κ - 1) n := by
    ring
  rw [hcount] at h₄
  exact rank_le_iff.mpr h₄

/-! ## The split at the level of admissible polynomial exponents -/

/-- **Splitting law for admissible exponents.**  If `τ₁` is an admissible polynomial exponent for
the `κ₁`-rectangular ranks and `τ₂` for the `κ₂`-rectangular ranks, then `θτ₁ + (1-θ)τ₂` is
admissible for the `(θκ₁ + (1-θ)κ₂)`-rectangular ranks, for `0 ≤ θ ≤ 1` and `κ₁, κ₂ ≥ 0`.

Proof sketch: combine the finite splitting law `rectangularMatrixRankSequence_le_mul_split` with
the two hypotheses evaluated at the split dimensions `n₁ = ⌈n^θ⌉ ≥ 1` and `n₂ = ⌈n^(1-θ)⌉ ≥ 1`:

`rank ≤ (C₁·n₁^τ₁)·(C₂·n₂^τ₂) ≤ (C₁·(2n^θ)^τ₁)·(C₂·(2n^(1-θ))^τ₂)
      = (C₁C₂2^τ₁2^τ₂)·n^(θτ₁+(1-θ)τ₂)`,

where the middle step is `rectangularMiddleDimension_le_two_mul_rpow` raised to the nonnegative
powers `τ₁, τ₂`.  The two rounding factors of `2^τᵢ` are constants and are absorbed into the
polynomial-bound constant, so the exponent is exact. -/
theorem rectangularMatrixExponentLE_split
    {κ₁ κ₂ θ τ₁ τ₂ : ℝ} (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (h₁ : RectangularMatrixExponentLE K κ₁ τ₁)
    (h₂ : RectangularMatrixExponentLE K κ₂ τ₂) :
    RectangularMatrixExponentLE K (θ * κ₁ + (1 - θ) * κ₂) (θ * τ₁ + (1 - θ) * τ₂) := by
  obtain ⟨hτ₁, C₁, hC₁, hb₁⟩ := h₁
  obtain ⟨hτ₂, C₂, hC₂, hb₂⟩ := h₂
  have hθ' : (0 : ℝ) ≤ 1 - θ := by linarith
  refine ⟨add_nonneg (mul_nonneg hθ₀ hτ₁) (mul_nonneg hθ' hτ₂),
    C₁ * C₂ * 2 ^ τ₁ * 2 ^ τ₂, by positivity, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  have hn₁ : 1 ≤ rectangularMiddleDimension θ n := rectangularMiddleDimension_pos θ hn
  have hn₂ : 1 ≤ rectangularMiddleDimension (1 - θ) n :=
    rectangularMiddleDimension_pos (1 - θ) hn
  have hsplit := rectangularMatrixRankSequence_le_mul_split K (θ := θ) hκ₁ hκ₂ hn
  -- Rounding estimates for the two split dimensions, raised to the two exponents.
  have hpow₁ : ((rectangularMiddleDimension θ n : ℕ) : ℝ) ^ τ₁ ≤ 2 ^ τ₁ * (n : ℝ) ^ (θ * τ₁) := by
    calc
      ((rectangularMiddleDimension θ n : ℕ) : ℝ) ^ τ₁ ≤ (2 * (n : ℝ) ^ θ) ^ τ₁ :=
        Real.rpow_le_rpow (Nat.cast_nonneg _)
          (rectangularMiddleDimension_le_two_mul_rpow hθ₀ hn) hτ₁
      _ = 2 ^ τ₁ * ((n : ℝ) ^ θ) ^ τ₁ :=
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnpos.le θ)
      _ = 2 ^ τ₁ * (n : ℝ) ^ (θ * τ₁) := by rw [← Real.rpow_mul hnpos.le]
  have hpow₂ : ((rectangularMiddleDimension (1 - θ) n : ℕ) : ℝ) ^ τ₂ ≤
      2 ^ τ₂ * (n : ℝ) ^ ((1 - θ) * τ₂) := by
    calc
      ((rectangularMiddleDimension (1 - θ) n : ℕ) : ℝ) ^ τ₂ ≤ (2 * (n : ℝ) ^ (1 - θ)) ^ τ₂ :=
        Real.rpow_le_rpow (Nat.cast_nonneg _)
          (rectangularMiddleDimension_le_two_mul_rpow hθ' hn) hτ₂
      _ = 2 ^ τ₂ * ((n : ℝ) ^ (1 - θ)) ^ τ₂ :=
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnpos.le _)
      _ = 2 ^ τ₂ * (n : ℝ) ^ ((1 - θ) * τ₂) := by rw [← Real.rpow_mul hnpos.le]
  have hb₁' := hb₁ _ hn₁
  have hb₂' := hb₂ _ hn₂
  calc
    (rectangularMatrixRankSequence K (θ * κ₁ + (1 - θ) * κ₂) n : ℝ)
        ≤ ((rectangularMatrixRankSequence K κ₁ (rectangularMiddleDimension θ n) *
              rectangularMatrixRankSequence K κ₂
                (rectangularMiddleDimension (1 - θ) n) : ℕ) : ℝ) := by
          exact_mod_cast hsplit
    _ = (rectangularMatrixRankSequence K κ₁ (rectangularMiddleDimension θ n) : ℝ) *
          (rectangularMatrixRankSequence K κ₂
            (rectangularMiddleDimension (1 - θ) n) : ℝ) := by push_cast; ring
    _ ≤ (C₁ * ((rectangularMiddleDimension θ n : ℕ) : ℝ) ^ τ₁) *
          (C₂ * ((rectangularMiddleDimension (1 - θ) n : ℕ) : ℝ) ^ τ₂) :=
      mul_le_mul hb₁' hb₂' (Nat.cast_nonneg _) (by positivity)
    _ ≤ (C₁ * (2 ^ τ₁ * (n : ℝ) ^ (θ * τ₁))) * (C₂ * (2 ^ τ₂ * (n : ℝ) ^ ((1 - θ) * τ₂))) := by
      gcongr
    _ = (C₁ * C₂ * 2 ^ τ₁ * 2 ^ τ₂) * ((n : ℝ) ^ (θ * τ₁) * (n : ℝ) ^ ((1 - θ) * τ₂)) := by ring
    _ = (C₁ * C₂ * 2 ^ τ₁ * 2 ^ τ₂) * (n : ℝ) ^ (θ * τ₁ + (1 - θ) * τ₂) := by
      rw [← Real.rpow_add hnpos]

/-- **Blocking law for admissible exponents.**  If `τ` is an admissible polynomial exponent for
square matrix multiplication, then `τ + (κ - 1)` is admissible for the `κ`-rectangular ranks, for
every `κ ≥ 1`.

Proof sketch: `rank ⟨n, ⌈n^κ⌉, n⟩ ≤ rank ⟨n,n,n⟩ · ⌈n^(κ-1)⌉ ≤ (C·n^τ)·(2·n^(κ-1))`, and the
factor two is absorbed into the constant. -/
theorem rectangularMatrixExponentLE_block
    {κ τ : ℝ} (hκ : 1 ≤ κ) (h : MatrixExponentLE K τ) :
    RectangularMatrixExponentLE K κ (τ + (κ - 1)) := by
  obtain ⟨hτ, C, hC, hb⟩ := h
  have hκ' : (0 : ℝ) ≤ κ - 1 := by linarith
  refine ⟨by linarith, 2 * C, by positivity, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  have hblock := rectangularMatrixRankSequence_le_mul_block K κ hn
  have hb' := hb n hn
  calc
    (rectangularMatrixRankSequence K κ n : ℝ)
        ≤ ((squareMatrixRankSequence K n * rectangularMiddleDimension (κ - 1) n : ℕ) : ℝ) := by
          exact_mod_cast hblock
    _ = (squareMatrixRankSequence K n : ℝ) *
          ((rectangularMiddleDimension (κ - 1) n : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (C * (n : ℝ) ^ τ) * (2 * (n : ℝ) ^ (κ - 1)) :=
      mul_le_mul hb' (rectangularMiddleDimension_le_two_mul_rpow hκ' hn)
        (Nat.cast_nonneg _) (by positivity)
    _ = (2 * C) * ((n : ℝ) ^ τ * (n : ℝ) ^ (κ - 1)) := by ring
    _ = (2 * C) * (n : ℝ) ^ (τ + (κ - 1)) := by rw [← Real.rpow_add hnpos]

/-! ## Transfer to the exponent

`rectangularOmega` is an infimum, so an inequality between admissible exponents becomes an
inequality between exponents only after an `ε`-argument.  The upper-closure lemma below is the
rectangular analogue of `matrixExponentLE_of_omega_lt`. -/

/-- Every real exponent strictly above `ω(κ)` is an admissible uniform polynomial rank bound for
the `κ`-rectangular family.  This is the usable upper-closure property of the defining infimum.

Proof sketch: the defining set of admissible exponents is nonempty
(`rectangularMatrixExponentLE_exists`), so `exists_lt_of_csInf_lt` produces an admissible `σ < τ`,
and `PolynomialBound.mono_exponent` raises `σ` to `τ`. -/
theorem rectangularMatrixExponentLE_of_rectangularOmega_lt {κ τ : ℝ}
    (hτ : rectangularOmega K κ < τ) :
    RectangularMatrixExponentLE K κ τ := by
  have hnonempty : Set.Nonempty
      {σ : ℝ | PolynomialBound (rectangularMatrixRankSequence K κ) σ} :=
    rectangularMatrixExponentLE_exists K κ
  obtain ⟨σ, hσ, hστ⟩ := exists_lt_of_csInf_lt hnonempty hτ
  exact hσ.mono_exponent hστ.le

/-! ## Convexity of the rectangular exponent -/

/-- **Convexity of `κ ↦ ω(κ)` on `[0, ∞)`.**  For `κ₁, κ₂ ≥ 0` and `0 ≤ θ ≤ 1`,

`ω(θ·κ₁ + (1-θ)·κ₂) ≤ θ·ω(κ₁) + (1-θ)·ω(κ₂)`,

over every commutative semiring.

Proof sketch: for `ε > 0` both `ω(κ₁) + ε/2` and `ω(κ₂) + ε/2` are admissible exponents by
`rectangularMatrixExponentLE_of_rectangularOmega_lt`, so `rectangularMatrixExponentLE_split`
makes `θ(ω(κ₁) + ε/2) + (1-θ)(ω(κ₂) + ε/2) = θω(κ₁) + (1-θ)ω(κ₂) + ε/2` admissible for the
convex combination, whence `ω(θκ₁ + (1-θ)κ₂) ≤ θω(κ₁) + (1-θ)ω(κ₂) + ε`.  Letting `ε ↓ 0` via
`le_of_forall_pos_le_add` finishes.  The weight `θ + (1-θ) = 1` is what turns the two `ε/2` terms
into a single `ε/2`. -/
theorem rectangularOmega_split_le
    {κ₁ κ₂ θ : ℝ} (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    rectangularOmega K (θ * κ₁ + (1 - θ) * κ₂) ≤
      θ * rectangularOmega K κ₁ + (1 - θ) * rectangularOmega K κ₂ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hlt₁ : rectangularOmega K κ₁ < rectangularOmega K κ₁ + ε / 2 := by linarith
  have hlt₂ : rectangularOmega K κ₂ < rectangularOmega K κ₂ + ε / 2 := by linarith
  have hsplit := rectangularMatrixExponentLE_split K hκ₁ hκ₂ hθ₀ hθ₁
    (rectangularMatrixExponentLE_of_rectangularOmega_lt K hlt₁)
    (rectangularMatrixExponentLE_of_rectangularOmega_lt K hlt₂)
  have hle := rectangularOmega_le K hsplit
  have hsimp : θ * (rectangularOmega K κ₁ + ε / 2) + (1 - θ) * (rectangularOmega K κ₂ + ε / 2) =
      θ * rectangularOmega K κ₁ + (1 - θ) * rectangularOmega K κ₂ + ε / 2 := by ring
  rw [hsimp] at hle
  linarith

/-- Packaged Mathlib form of the previous theorem: `κ ↦ ω(κ)` is a convex function on the ray
`[0, ∞)`, over every commutative semiring. -/
theorem rectangularOmega_convexOn :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (rectangularOmega K) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  simpa only [smul_eq_mul] using
    rectangularOmega_split_le K hx hy ha (by linarith)

/-- **Chord bound.**  Upper bounds `A` at `a` and `B` at `b` on the rectangular exponent bound
it on the whole segment `[a, b]` by the chord through `(a, A)` and `(b, B)`:

```text
ω(κ)  ≤  ((b − κ)·A + (κ − a)·B) / (b − a)        for 0 ≤ a ≤ κ ≤ b, a < b.
```

This is convexity (`rectangularOmega_split_le`) with the weights `(b − κ)/(b − a)` and
`(κ − a)/(b − a)`; it is the form in which two numerical bounds on `ω(·)` are interpolated. -/
theorem rectangularOmega_le_chord {a b κ A B : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (haκ : a ≤ κ) (hκb : κ ≤ b) (hA : rectangularOmega K a ≤ A) (hB : rectangularOmega K b ≤ B) :
    rectangularOmega K κ ≤ ((b - κ) * A + (κ - a) * B) / (b - a) := by
  have hden : 0 < b - a := by linarith
  set θ : ℝ := (b - κ) / (b - a) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hden.le
  have hθ1 : θ ≤ 1 := (div_le_one hden).mpr (by linarith)
  have h1θ : 1 - θ = (κ - a) / (b - a) := by
    rw [hθ]
    field_simp
    ring
  have hκ : θ * a + (1 - θ) * b = κ := by
    rw [h1θ, hθ]
    field_simp
    ring
  have h := rectangularOmega_split_le K ha (ha.trans hab.le) hθ0 hθ1
  rw [hκ] at h
  calc rectangularOmega K κ
      ≤ θ * rectangularOmega K a + (1 - θ) * rectangularOmega K b := h
    _ ≤ θ * A + (1 - θ) * B :=
      add_le_add (mul_le_mul_of_nonneg_left hA hθ0)
        (mul_le_mul_of_nonneg_left hB (by linarith))
    _ = ((b - κ) * A + (κ - a) * B) / (b - a) := by
      rw [h1θ, hθ]
      field_simp

/-- Midpoint form of convexity, stated separately because it is the shape used in the limiting
argument for `α = 1 → ω = 2`. -/
theorem rectangularOmega_midpoint_le {κ₁ κ₂ : ℝ} (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) :
    rectangularOmega K ((κ₁ + κ₂) / 2) ≤
      (rectangularOmega K κ₁ + rectangularOmega K κ₂) / 2 := by
  have h := rectangularOmega_split_le K hκ₁ hκ₂ (θ := 1 / 2) (by norm_num) (by norm_num)
  have hindex : (1 : ℝ) / 2 * κ₁ + (1 - 1 / 2) * κ₂ = (κ₁ + κ₂) / 2 := by ring
  have hvalue : (1 : ℝ) / 2 * rectangularOmega K κ₁ + (1 - 1 / 2) * rectangularOmega K κ₂ =
      (rectangularOmega K κ₁ + rectangularOmega K κ₂) / 2 := by ring
  rwa [hindex, hvalue] at h

/-! ## The interpolation upper bound -/

/-- **Interpolation upper bound.**  For `0 ≤ κ ≤ 1`,

`ω(κ) ≤ κ·ω + 2·(1 - κ)`,

over every commutative semiring.  At `κ = 1` this is the identity `ω(1) = ω`; at `κ = 0` it is
the outer-product bound `ω(0) ≤ 2`; in between it interpolates linearly between them.

Proof sketch: this is the split at `(κ₁, κ₂, θ) = (1, 0, κ)`, that is, the external product

`⟨n, ⌈n^κ⌉, n⟩ ⪯ ⟨⌈n^κ⌉, ⌈n^κ⌉, ⌈n^κ⌉⟩ ⊗ ⟨⌈n^(1-κ)⌉, 1, ⌈n^(1-κ)⌉⟩`,

whose first factor is a square product of side `n^κ` — cost `n^(κω)` — and whose second factor is
an outer product of two vectors of length `n^(1-κ)` — cost `n^(2(1-κ))`.  Formally,
`rectangularOmega_split_le` gives `ω(κ) ≤ κ·ω(1) + (1-κ)·ω(0)`, and then `ω(1) = ω`
(`rectangularOmega_one`) together with `ω(0) ≤ 2` (`rectangularOmega_le_two_add_max` at `κ = 0`)
finishes.  Since `1 - κ ≥ 0`, the estimate `ω(0) ≤ 2` may be substituted with the correct
direction. -/
theorem rectangularOmega_le_interpolation {κ : ℝ} (hκ₀ : 0 ≤ κ) (hκ₁ : κ ≤ 1) :
    rectangularOmega K κ ≤ κ * omega K + 2 * (1 - κ) := by
  have hsplit := rectangularOmega_split_le K (κ₁ := 1) (κ₂ := 0) (θ := κ)
    zero_le_one le_rfl hκ₀ hκ₁
  have hindex : κ * (1 : ℝ) + (1 - κ) * 0 = κ := by ring
  rw [hindex, rectangularOmega_one] at hsplit
  have hzero : rectangularOmega K 0 ≤ 2 := by
    have h := rectangularOmega_le_two_add_max K 0
    simpa using h
  nlinarith [hsplit, hzero, sub_nonneg.mpr hκ₁]

/-- Long-name form of the interpolation upper bound `ω(κ) ≤ κ·ω + 2·(1 - κ)`. -/
theorem rectangularMatrixMultiplicationExponent_le_interpolation {κ : ℝ}
    (hκ₀ : 0 ≤ κ) (hκ₁ : κ ≤ 1) :
    rectangularMatrixMultiplicationExponent K κ ≤
      κ * matrixMultiplicationExponent K + 2 * (1 - κ) :=
  rectangularOmega_le_interpolation K hκ₀ hκ₁

/-! ## The blocking upper bound for `κ ≥ 1` -/

/-- **Blocking upper bound.**  For `κ ≥ 1`,

`ω(κ) ≤ ω + (κ - 1)`,

over every commutative semiring: an `n × n^κ` by `n^κ × n` product decomposes into `n^(κ-1)`
square products of side `n`.

Proof sketch: for `ε > 0` the exponent `ω + ε` is admissible for square multiplication
(`matrixExponentLE_of_omega_lt`), so `rectangularMatrixExponentLE_block` makes
`(ω + ε) + (κ - 1)` admissible for the `κ`-rectangular family; let `ε ↓ 0`. -/
theorem rectangularOmega_le_omega_add_sub_one {κ : ℝ} (hκ : 1 ≤ κ) :
    rectangularOmega K κ ≤ omega K + (κ - 1) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hlt : omega K < omega K + ε := by linarith
  have hblock := rectangularMatrixExponentLE_block K hκ (matrixExponentLE_of_omega_lt K hlt)
  have hle := rectangularOmega_le K hblock
  linarith

/-- Long-name form of the blocking upper bound `ω(κ) ≤ ω + (κ - 1)` for `κ ≥ 1`. -/
theorem rectangularMatrixMultiplicationExponent_le_add_sub_one {κ : ℝ} (hκ : 1 ≤ κ) :
    rectangularMatrixMultiplicationExponent K κ ≤
      matrixMultiplicationExponent K + (κ - 1) :=
  rectangularOmega_le_omega_add_sub_one K hκ

/-! ## Corollaries in terms of the dual exponent -/

/-- **Lotti–Romani interpolation formula, in witnessed form.**  If `κ₀` is *any* exponent with
`ω(κ₀) = 2` and `0 ≤ κ₀ < 1`, then for every `κ₀ ≤ κ ≤ 1`

`ω(κ) ≤ 2 + (ω - 2)·(κ - κ₀)/(1 - κ₀)`.

The theorem is stated for an arbitrary witness `κ₀` because that is what convexity needs and
because it holds over every commutative semiring.  The classical statement is the case
`κ₀ = α`, available over a field as `rectangularOmega_le_interpolation_rectangularAlpha` once
`rectangularOmega_rectangularAlpha` shows the supremum defining `rectangularAlpha` is attained.

Proof sketch: apply convexity at `(κ₁, κ₂, θ) = (1, κ₀, (κ - κ₀)/(1 - κ₀))`.  The weight lies in
`[0, 1]` exactly because `κ₀ ≤ κ ≤ 1` and `κ₀ < 1`, and the convex combination
`θ·1 + (1-θ)·κ₀ = κ₀ + θ(1 - κ₀)` is `κ`.  The value bound is then
`θ·ω + (1-θ)·2 = 2 + θ(ω - 2)`. -/
theorem rectangularOmega_le_interpolation_of_eq_two
    {κ κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ₀one : κ₀ < 1) (hbase : rectangularOmega K κ₀ = 2)
    (hle : κ₀ ≤ κ) (hle1 : κ ≤ 1) :
    rectangularOmega K κ ≤ 2 + (omega K - 2) * (κ - κ₀) / (1 - κ₀) := by
  set θ : ℝ := (κ - κ₀) / (1 - κ₀) with hθdef
  have hden : (0 : ℝ) < 1 - κ₀ := by linarith
  have hθ₀ : 0 ≤ θ := by
    rw [hθdef]
    exact div_nonneg (by linarith) hden.le
  have hθ₁ : θ ≤ 1 := by
    rw [hθdef, div_le_one hden]
    linarith
  have hsplit := rectangularOmega_split_le K (κ₁ := 1) (κ₂ := κ₀) (θ := θ)
    zero_le_one hκ₀ hθ₀ hθ₁
  have hindex : θ * (1 : ℝ) + (1 - θ) * κ₀ = κ := by
    rw [hθdef]
    field_simp
    ring
  rw [hindex, rectangularOmega_one, hbase] at hsplit
  have hvalue : θ * omega K + (1 - θ) * 2 = 2 + (omega K - 2) * (κ - κ₀) / (1 - κ₀) := by
    rw [hθdef]
    field_simp
    ring
  rwa [hvalue] at hsplit

section FieldCorollaries

variable (F : Type u) [Field F]

/-- **The supremum defining the dual exponent is attained**: over a field,
`ω(α) = 2`.

The defining set of `rectangularAlpha` is a supremum, so attainment is not formal; the convexity
of `κ ↦ ω(κ)` proved above supplies exactly the missing regularity.  Together with
`rectangularOmega_eq_two_of_lt_rectangularAlpha` this says
that `[0, α]` — a closed interval — is precisely the region where the rectangular exponent is
optimal, and it lets `rectangularOmega_le_interpolation_of_eq_two` be applied at the classical
witness `κ₀ = α`.

Proof sketch: for `α = 0` this is `rectangularOmega_zero`.  For `α > 0` and `0 < δ < α`, write
`α` as the convex combination `θ·(α - δ) + (1 - θ)·(α + 1)` with `θ = 1/(1 + δ)`.  The left
endpoint lies strictly below `α`, so `ω(α - δ) = 2`, and the right endpoint has the finite
value `M = ω(α + 1)`.  Convexity therefore gives `ω(α) ≤ (2 + δ·M)/(1 + δ) ≤ 2 + δ·M`, and
`δ ↓ 0` forces `ω(α) ≤ 2`; the flattening bound `2 ≤ ω(α)` gives equality. -/
theorem rectangularOmega_rectangularAlpha :
    rectangularOmega F (rectangularAlpha F) = 2 := by
  refine le_antisymm ?_ (two_le_rectangularOmega F _)
  set α : ℝ := rectangularAlpha F with hαdef
  have hα0 : 0 ≤ α := rectangularAlpha_nonneg F
  rcases eq_or_lt_of_le hα0 with hzero | hpos
  · rw [← hzero]
    exact (rectangularOmega_zero F).le
  · set M : ℝ := rectangularOmega F (α + 1) with hMdef
    have hM : 0 < M := lt_of_lt_of_le two_pos (two_le_rectangularOmega F _)
    apply le_of_forall_pos_le_add
    intro ε hε
    set δ : ℝ := min (ε / M) (α / 2) with hδdef
    have hδpos : 0 < δ := lt_min (div_pos hε hM) (by linarith)
    have hδα : δ < α := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hδε : δ * M ≤ ε := by
      have h := min_le_left (ε / M) (α / 2)
      calc δ * M ≤ (ε / M) * M := by nlinarith
        _ = ε := div_mul_cancel₀ ε hM.ne'
    have hlow : rectangularOmega F (α - δ) = 2 :=
      rectangularOmega_eq_two_of_lt_rectangularAlpha F (by rw [← hαdef]; linarith)
    have hden : (0 : ℝ) < 1 + δ := by linarith
    have hθ₀ : (0 : ℝ) ≤ 1 / (1 + δ) := by positivity
    have hθ₁ : 1 / (1 + δ) ≤ 1 := by
      rw [div_le_one hden]; linarith
    have hsplit := rectangularOmega_split_le F (κ₁ := α - δ) (κ₂ := α + 1)
      (θ := 1 / (1 + δ)) (by linarith) (by linarith) hθ₀ hθ₁
    have hindex : 1 / (1 + δ) * (α - δ) + (1 - 1 / (1 + δ)) * (α + 1) = α := by
      field_simp
      ring
    rw [hindex, hlow, ← hMdef] at hsplit
    have hvalue : 1 / (1 + δ) * 2 + (1 - 1 / (1 + δ)) * M = (2 + δ * M) / (1 + δ) := by
      field_simp
      ring
    rw [hvalue] at hsplit
    have hfrac : (2 + δ * M) / (1 + δ) ≤ 2 + δ * M := by
      rw [div_le_iff₀ hden]
      have h1 : (0 : ℝ) ≤ 2 + δ * M := by positivity
      nlinarith
    linarith

/-- **The Lotti--Romani interpolation formula at the dual exponent itself.**  Over a field with
`α < 1`, for every `α ≤ κ ≤ 1`,

`ω(κ) ≤ 2 + (ω - 2)·(κ - α)/(1 - α)`.

This is the classical statement, now available because `rectangularOmega_rectangularAlpha`
shows the supremum defining `α` is attained. -/
theorem rectangularOmega_le_interpolation_rectangularAlpha
    (hα : rectangularAlpha F < 1) {κ : ℝ}
    (hle : rectangularAlpha F ≤ κ) (hle1 : κ ≤ 1) :
    rectangularOmega F κ ≤
      2 + (omega F - 2) * (κ - rectangularAlpha F) / (1 - rectangularAlpha F) :=
  rectangularOmega_le_interpolation_of_eq_two F (rectangularAlpha_nonneg F) hα
    (rectangularOmega_rectangularAlpha F) hle hle1

/-- Over a field, `α = 1` forces `ω = 2`.  This is the converse direction that
`RectangularExponent.lean` records as future work; convexity supplies the missing regularity of
`κ ↦ ω(κ)` at `κ = 1`.

Proof sketch: fix `δ ∈ (0, 1/2]`.  Since `1 - δ < 1 = α`, the previous corollary gives
`ω(1 - δ) = 2`, and the blocking bound gives `ω(1 + δ) ≤ ω + δ`.  Convexity at the midpoint of
`1 - δ` and `1 + δ`, which is `1`, then gives

`ω = ω(1) ≤ (ω(1-δ) + ω(1+δ))/2 ≤ (2 + ω + δ)/2`,

i.e. `ω ≤ 2 + δ`.  Since `δ > 0` is arbitrary, `ω ≤ 2`; the flattening bound `2 ≤ ω` gives
equality.  The role of `α = 1` is only to make `ω(1 - δ) = 2` available for every small `δ`; the
role of the blocking bound is to keep `ω(1 + δ)` under control on the other side, so that `1` is
an interior point of a segment on which convexity can be used. -/
theorem omega_eq_two_of_rectangularAlpha_eq_one (h : rectangularAlpha F = 1) :
    omega F = 2 := by
  refine le_antisymm ?_ (two_le_omega F)
  apply le_of_forall_pos_le_add
  intro ε hε
  set δ : ℝ := min ε (1 / 2) with hδdef
  have hδpos : 0 < δ := lt_min hε (by norm_num)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hlow : rectangularOmega F (1 - δ) = 2 := by
    apply rectangularOmega_eq_two_of_lt_rectangularAlpha
    rw [h]
    linarith
  have hhigh : rectangularOmega F (1 + δ) ≤ omega F + δ := by
    have := rectangularOmega_le_omega_add_sub_one F (κ := 1 + δ) (by linarith)
    linarith
  have hmid := rectangularOmega_midpoint_le F (κ₁ := 1 - δ) (κ₂ := 1 + δ)
    (by linarith) (by linarith)
  have hindex : ((1 - δ) + (1 + δ)) / 2 = (1 : ℝ) := by ring
  rw [hindex, rectangularOmega_one, hlow] at hmid
  linarith

/-- Over a field, the dual exponent is `1` exactly when the square exponent is `2`.  The reverse
direction is `rectangularAlpha_eq_one_of_omega_eq_two` from `RectangularExponent.lean`; the
forward direction is `omega_eq_two_of_rectangularAlpha_eq_one`. -/
theorem rectangularAlpha_eq_one_iff_omega_eq_two :
    rectangularAlpha F = 1 ↔ omega F = 2 :=
  ⟨omega_eq_two_of_rectangularAlpha_eq_one F, rectangularAlpha_eq_one_of_omega_eq_two F⟩

end FieldCorollaries

end AlgebraicComplexity
