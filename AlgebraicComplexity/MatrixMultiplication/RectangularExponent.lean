/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.Exponent

/-!
# The rectangular matrix-multiplication exponent

This module defines the rectangular matrix-multiplication exponent `rectangularOmega K κ`,
written `ω(κ)` below: the least real exponent giving a uniform polynomial upper bound on the
ranks of the rectangular matrix-multiplication tensors `⟨n, ⌈n^κ⌉, n⟩` over a coefficient
semiring `K`.  Here the middle dimension is `rectangularMiddleDimension κ n = ⌈(n : ℝ)^κ⌉₊`,
so `ω(κ)` measures the cost of multiplying an `n × n^κ` matrix by an `n^κ × n` matrix; in the
notation of the rectangular literature it is `ω(1, κ, 1)`.

## Principal results

* `rectangularOmega_le_two_add`: the defining decomposition gives `ω(κ) ≤ 2 + κ` for `κ ≥ 0`,
  over every commutative semiring (and `ω(κ) ≤ 2 + max κ 0` with no sign hypothesis);
* `rectangularOmega_mono`: `ω` is monotone in `κ`, over every commutative semiring;
* `rectangularOmega_one`: at `κ = 1` the middle dimension `⌈n^1⌉` is exactly `n`, so `ω(1)`
  literally equals the square exponent `omega K` — an equality of infima, not just a pair of
  inequalities;
* `two_le_rectangularOmega` and `one_add_le_rectangularOmega`: over a field, flattening the
  concise tensor `⟨n, ⌈n^κ⌉, n⟩` on its legs gives `max 2 (1 + κ) ≤ ω(κ)`.  In particular the
  familiar bound `2 ≤ ω(κ)` holds for every real `κ`, while `1 + κ ≤ ω(κ)` is the binding
  constraint for `κ > 1`;
* `rectangularOmega_zero`: over a field, `ω(0) = 2` exactly: `⟨n, 1, n⟩` is an outer product
  of rank exactly `n²`;
* `rectangularAlpha`: the dual exponent `α = sSup {κ | 0 ≤ κ ∧ ω(κ) = 2}`.  Over a field the
  set is nonempty (it contains `0`) and bounded above by `1` (because `1 + κ ≤ ω(κ)`), so the
  supremum is well behaved: `0 ≤ α ≤ 1` (`rectangularAlpha_nonneg`, `rectangularAlpha_le_one`)
  and `α = 1` whenever `ω = 2` (`rectangularAlpha_eq_one_of_omega_eq_two`);
* `rectangularOmega_eq_two_of_le` and `rectangularOmega_eq_two_of_lt_rectangularAlpha`: over a
  field the region of optimality is downward closed, and contains all of `[0, α)`.  Attainment
  at `α` itself needs convexity and is proved downstream, in
  `MatrixMultiplication/RectangularInterpolation.lean`.

## Layer placement and strategy

This is a leaf module of the matrix-multiplication theory layer, downstream of
`MatrixMultiplication/Exponent.lean`, whose conventions it mirrors exactly: the exponent is the
`sInf` of the set of admissible real exponents `τ` in `Growth.PolynomialBound`, upper bounds
come from `polynomialExponent_le` applied to explicit rank certificates
(`matrixMultiplication_rankLE`), and lower bounds come from conciseness flattenings
(`MatrixMultiplication/Concise.lean`) fed through `le_csInf`.  Rank monotonicity in the middle
dimension is obtained from `matrixMultiplication_restricts`.

## Non-goals and future work

* Nontrivial rectangular upper bounds (Coppersmith's `α > 0.172`, Huang–Pan's improvements)
  are downstream client material, exercising `RectangularMatrixExponentLE`.
* Convexity of `κ ↦ ω(κ)`, the interpolation and Lotti–Romani bounds, and the equivalence
  `α = 1 ↔ ω = 2` are now proved in `MatrixMultiplication/RectangularInterpolation.lean`
  (the convexity regularity supplied there replaces the continuity argument this file
  originally deferred).
* An arithmetic-complexity reading of `ω(κ)` is still missing.  The square case now has one —
  `MatrixMultiplication/BilinearAlgorithm.lean` compiles a rank certificate into a circuit and
  `MatrixMultiplication/RankComplexityRecursion.lean` iterates that into
  `exists_straightline_matrixProduct_of_omega_lt` — but there is no rectangular analogue of that
  recursion, whose block step would have to keep the middle dimension at `⌈n^κ⌉` under powering.

## References

* D. Coppersmith, *Rapid multiplication of rectangular matrices*, SIAM J. Comput. 11 (1982).
* D. Coppersmith, *Rectangular matrix multiplication revisited*, J. Complexity 13 (1997).
* X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity 14 (1998).
-/

namespace AlgebraicComplexity

open Tensor Growth

universe u

/-! ## The rectangular rank sequence and its exponent -/

/-- The middle dimension of the `κ`-rectangular family: the ceiling `⌈(n : ℝ)^κ⌉₊`.

Edge conventions follow `Nat.ceil` and `Real.rpow`: at `n = 1` the value is `1` for every `κ`;
at `n = 0` it is `1` for `κ = 0` and `0` otherwise.  Both `n = 0` values are harmless because
`Growth.PolynomialBound` only constrains positive inputs. -/
noncomputable def rectangularMiddleDimension (κ : ℝ) (n : ℕ) : ℕ :=
  ⌈(n : ℝ) ^ κ⌉₊

/-- At `κ = 1` the middle dimension is exactly `n`, with no rounding. -/
@[simp] theorem rectangularMiddleDimension_one (n : ℕ) :
    rectangularMiddleDimension 1 n = n := by
  unfold rectangularMiddleDimension
  rw [Real.rpow_one, Nat.ceil_natCast]

/-- At `κ = 0` the middle dimension is exactly `1`, for every `n`. -/
@[simp] theorem rectangularMiddleDimension_zero (n : ℕ) :
    rectangularMiddleDimension 0 n = 1 := by
  unfold rectangularMiddleDimension
  rw [Real.rpow_zero, Nat.ceil_one]

/-- The defining inequality of the ceiling: `n^κ ≤ ⌈n^κ⌉`. -/
theorem rpow_le_rectangularMiddleDimension (κ : ℝ) (n : ℕ) :
    (n : ℝ) ^ κ ≤ rectangularMiddleDimension κ n :=
  Nat.le_ceil _

/-- The middle dimension is positive whenever `n` is. -/
theorem rectangularMiddleDimension_pos (κ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    0 < rectangularMiddleDimension κ n :=
  Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) κ)

/-- For fixed positive `n`, the middle dimension is monotone in the exponent `κ`. -/
theorem rectangularMiddleDimension_mono {n : ℕ} (hn : 1 ≤ n) {κ κ' : ℝ}
    (h : κ ≤ κ') :
    rectangularMiddleDimension κ n ≤ rectangularMiddleDimension κ' n :=
  Nat.ceil_mono
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) h)

/-- Rounding up costs at most a factor two: `⌈n^κ⌉ ≤ 2·n^κ` for `κ ≥ 0` and `n ≥ 1`.

Proof sketch: `⌈x⌉₊ < x + 1` for `x ≥ 0`, and `x = n^κ ≥ 1` because `n ≥ 1` and `κ ≥ 0`, so
`x + 1 ≤ 2x`. -/
theorem rectangularMiddleDimension_le_two_mul_rpow {κ : ℝ} (hκ : 0 ≤ κ) {n : ℕ}
    (hn : 1 ≤ n) :
    (rectangularMiddleDimension κ n : ℝ) ≤ 2 * (n : ℝ) ^ κ := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ κ := Real.one_le_rpow hn1 hκ
  have hlt : (rectangularMiddleDimension κ n : ℝ) < (n : ℝ) ^ κ + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) κ)
  linarith

variable (K : Type u) [CommSemiring K]

/-- Ordinary ranks of the rectangular matrix-multiplication tensors `⟨n, ⌈n^κ⌉, n⟩` over `K`. -/
noncomputable def rectangularMatrixRankSequence (κ : ℝ) (n : ℕ) : ℕ :=
  rank (matrixMultiplication (K := K) n (rectangularMiddleDimension κ n) n)

/-- `τ` is a polynomial upper bound for the `κ`-rectangular matrix-multiplication ranks over
`K`. -/
abbrev RectangularMatrixExponentLE (κ τ : ℝ) : Prop :=
  PolynomialBound (rectangularMatrixRankSequence K κ) τ

/-- The rectangular matrix-multiplication exponent `ω(1, κ, 1)` over `K`: the least real `τ`
such that `rank ⟨n, ⌈n^κ⌉, n⟩ ≤ C·n^τ` for some constant `C` and all positive `n`. -/
noncomputable def rectangularMatrixMultiplicationExponent (κ : ℝ) : ℝ :=
  polynomialExponent (rectangularMatrixRankSequence K κ)

/-- Short conventional name for the rectangular matrix-multiplication exponent `ω(1, κ, 1)`. -/
noncomputable abbrev rectangularOmega (κ : ℝ) : ℝ :=
  rectangularMatrixMultiplicationExponent K κ

/-- The rectangular exponent is nonnegative, as an infimum of nonnegative bounds. -/
theorem rectangularMatrixMultiplicationExponent_nonneg (κ : ℝ) :
    0 ≤ rectangularMatrixMultiplicationExponent K κ :=
  polynomialExponent_nonneg _

/-- Short-name form: `0 ≤ ω(κ)`. -/
theorem rectangularOmega_nonneg (κ : ℝ) : 0 ≤ rectangularOmega K κ :=
  rectangularMatrixMultiplicationExponent_nonneg K κ

/-- A concrete polynomial rank bound gives an upper bound on the rectangular exponent. -/
theorem rectangularMatrixMultiplicationExponent_le {κ τ : ℝ}
    (h : RectangularMatrixExponentLE K κ τ) :
    rectangularMatrixMultiplicationExponent K κ ≤ τ :=
  polynomialExponent_le h

/-- Short-name form: a concrete polynomial rank bound `τ` gives `ω(κ) ≤ τ`. -/
theorem rectangularOmega_le {κ τ : ℝ} (h : RectangularMatrixExponentLE K κ τ) :
    rectangularOmega K κ ≤ τ :=
  rectangularMatrixMultiplicationExponent_le K h

/-! ## The trivial upper bound `ω(κ) ≤ 2 + κ` -/

/-- The defining `n·⌈n^κ⌉·n`-term decomposition bounds each rectangular rank. -/
theorem rectangularMatrixRankSequence_le_mul (κ : ℝ) (n : ℕ) :
    rectangularMatrixRankSequence K κ n ≤
      n * rectangularMiddleDimension κ n * n := by
  apply rank_le_iff.mpr
  exact matrixMultiplication_rankLE (K := K) n (rectangularMiddleDimension κ n) n

/-- The elementary algorithm gives the polynomial bound `2 + max κ 0` for every real `κ`,
with constant `2` absorbing the ceiling.

Proof sketch: for `n ≥ 1` the trivial decomposition gives
`rank ⟨n, ⌈n^κ⌉, n⟩ ≤ n·⌈n^κ⌉·n`, the ceiling satisfies `⌈n^κ⌉ < n^κ + 1 ≤ 2·n^(max κ 0)`
because `n^(max κ 0) ≥ 1`, and `n·n·n^(max κ 0) = n^(2 + max κ 0)`. -/
theorem rectangularMatrixExponentLE_two_add_max (κ : ℝ) :
    RectangularMatrixExponentLE K κ (2 + max κ 0) := by
  refine ⟨by have := le_max_right κ (0 : ℝ); linarith, 2, two_pos, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ max κ 0 :=
    Real.one_le_rpow hn1 (le_max_right κ 0)
  have hmid : (rectangularMiddleDimension κ n : ℝ) ≤ 2 * (n : ℝ) ^ max κ 0 :=
    le_trans (by exact_mod_cast rectangularMiddleDimension_mono hn (le_max_left κ 0))
      (rectangularMiddleDimension_le_two_mul_rpow (le_max_right κ 0) hn)
  have hsq : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) * (n : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  calc
    (rectangularMatrixRankSequence K κ n : ℝ)
        ≤ ((n * rectangularMiddleDimension κ n * n : ℕ) : ℝ) := by
          exact_mod_cast rectangularMatrixRankSequence_le_mul K κ n
    _ = (n : ℝ) * (rectangularMiddleDimension κ n : ℝ) * (n : ℝ) := by
          push_cast
          ring
    _ ≤ (n : ℝ) * (2 * (n : ℝ) ^ max κ 0) * (n : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hnpos.le
          exact mul_le_mul_of_nonneg_left hmid hnpos.le
    _ = 2 * ((n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ max κ 0) := by
          rw [hsq]
          ring
    _ = 2 * (n : ℝ) ^ (2 + max κ 0) := by
          rw [← Real.rpow_add hnpos]

/-- Every rectangular rank sequence admits some polynomial bound; this nonemptiness makes the
defining infimum of `rectangularOmega` well behaved for every real `κ`. -/
theorem rectangularMatrixExponentLE_exists (κ : ℝ) :
    ∃ τ, RectangularMatrixExponentLE K κ τ :=
  ⟨2 + max κ 0, rectangularMatrixExponentLE_two_add_max K κ⟩

/-- For `κ ≥ 0` the elementary algorithm gives the polynomial bound `2 + κ`. -/
theorem rectangularMatrixExponentLE_two_add {κ : ℝ} (hκ : 0 ≤ κ) :
    RectangularMatrixExponentLE K κ (2 + κ) := by
  have h := rectangularMatrixExponentLE_two_add_max K κ
  rwa [max_eq_left hκ] at h

/-- The trivial decomposition gives `ω(κ) ≤ 2 + max κ 0` for every real `κ`. -/
theorem rectangularMatrixMultiplicationExponent_le_two_add_max (κ : ℝ) :
    rectangularMatrixMultiplicationExponent K κ ≤ 2 + max κ 0 :=
  polynomialExponent_le (rectangularMatrixExponentLE_two_add_max K κ)

/-- Short-name form: `ω(κ) ≤ 2 + max κ 0` for every real `κ`. -/
theorem rectangularOmega_le_two_add_max (κ : ℝ) :
    rectangularOmega K κ ≤ 2 + max κ 0 :=
  rectangularMatrixMultiplicationExponent_le_two_add_max K κ

/-- The trivial decomposition gives `ω(κ) ≤ 2 + κ` for `κ ≥ 0`, over every commutative
semiring. -/
theorem rectangularMatrixMultiplicationExponent_le_two_add {κ : ℝ} (hκ : 0 ≤ κ) :
    rectangularMatrixMultiplicationExponent K κ ≤ 2 + κ :=
  polynomialExponent_le (rectangularMatrixExponentLE_two_add K hκ)

/-- Short-name form: `ω(κ) ≤ 2 + κ` for `κ ≥ 0`. -/
theorem rectangularOmega_le_two_add {κ : ℝ} (hκ : 0 ≤ κ) :
    rectangularOmega K κ ≤ 2 + κ :=
  rectangularMatrixMultiplicationExponent_le_two_add K hκ

/-! ## Monotonicity in `κ` -/

/-- For fixed positive `n`, enlarging `κ` enlarges the rectangular rank: the wider tensor
restricts onto the narrower one by dropping middle coordinates. -/
theorem rectangularMatrixRankSequence_mono {κ κ' : ℝ} (h : κ ≤ κ') {n : ℕ}
    (hn : 1 ≤ n) :
    rectangularMatrixRankSequence K κ n ≤ rectangularMatrixRankSequence K κ' n :=
  rank_restricts_le
    (matrixMultiplication_restricts (K := K) le_rfl
      (rectangularMiddleDimension_mono hn h) le_rfl)

/-- The rectangular exponent is monotone in `κ`: if `κ ≤ κ'` then `ω(κ) ≤ ω(κ')`.

Proof sketch: for every positive `n` the `κ`-rectangular tensor is a restriction of the
`κ'`-rectangular tensor, so every admissible polynomial bound for `κ'` is admissible for `κ`,
and the infimum over the larger set of bounds is smaller. -/
theorem rectangularMatrixMultiplicationExponent_mono {κ κ' : ℝ} (h : κ ≤ κ') :
    rectangularMatrixMultiplicationExponent K κ ≤
      rectangularMatrixMultiplicationExponent K κ' :=
  Growth.polynomialExponent_mono
    (fun _ hn ↦ rectangularMatrixRankSequence_mono K h hn)
    (rectangularMatrixExponentLE_exists K κ')

/-- Short-name form: `κ ≤ κ'` implies `ω(κ) ≤ ω(κ')`. -/
theorem rectangularOmega_mono {κ κ' : ℝ} (h : κ ≤ κ') :
    rectangularOmega K κ ≤ rectangularOmega K κ' :=
  rectangularMatrixMultiplicationExponent_mono K h

/-! ## The square case `κ = 1` -/

/-- At `κ = 1` the rectangular rank sequence coincides with the square rank sequence: the
ceiling of `n^1` is exactly `n`. -/
theorem rectangularMatrixRankSequence_one :
    rectangularMatrixRankSequence K 1 = squareMatrixRankSequence K := by
  funext n
  unfold rectangularMatrixRankSequence squareMatrixRankSequence
  rw [rectangularMiddleDimension_one]

/-- At `κ = 1` the rectangular exponent equals the square matrix-multiplication exponent:
`ω(1) = ω`.  This is an equality of the defining infima, because the two rank sequences are
literally equal. -/
theorem rectangularMatrixMultiplicationExponent_one :
    rectangularMatrixMultiplicationExponent K 1 = matrixMultiplicationExponent K := by
  unfold rectangularMatrixMultiplicationExponent matrixMultiplicationExponent
  rw [rectangularMatrixRankSequence_one]

/-- Short-name form: `ω(1) = ω`, an exact equality of the defining infima. -/
theorem rectangularOmega_one : rectangularOmega K 1 = omega K :=
  rectangularMatrixMultiplicationExponent_one K

/-- For `κ ≥ 1` the rectangular exponent dominates the square exponent: `ω ≤ ω(κ)`. -/
theorem omega_le_rectangularOmega {κ : ℝ} (h : 1 ≤ κ) :
    omega K ≤ rectangularOmega K κ :=
  (rectangularOmega_one K).symm.trans_le (rectangularOmega_mono K h)

/-- For `κ ≤ 1` the rectangular exponent is dominated by the square exponent: `ω(κ) ≤ ω`. -/
theorem rectangularOmega_le_omega {κ : ℝ} (h : κ ≤ 1) :
    rectangularOmega K κ ≤ omega K :=
  (rectangularOmega_mono K h).trans_eq (rectangularOmega_one K)

/-! ## Flattening lower bounds and the dual exponent, over a field -/

section FieldLowerBound

variable (F : Type u) [Field F]

/-- Flattening on the `X` leg gives the pointwise lower bound `n·⌈n^κ⌉ ≤ rank ⟨n, ⌈n^κ⌉, n⟩`
for positive `n`. -/
theorem mul_rectangularMiddleDimension_le_rectangularMatrixRankSequence
    (κ : ℝ) {n : ℕ} (hn : 0 < n) :
    n * rectangularMiddleDimension κ n ≤ rectangularMatrixRankSequence F κ n :=
  matrixMultiplication_rank_lower_X (K := F) hn
    (rank_spec (matrixMultiplication (K := F) n (rectangularMiddleDimension κ n) n))

/-- Flattening on the outer legs gives the pointwise quadratic lower bound
`n² ≤ rank ⟨n, ⌈n^κ⌉, n⟩`, for every real `κ`. -/
theorem sq_le_rectangularMatrixRankSequence (κ : ℝ) (n : ℕ) :
    n ^ 2 ≤ rectangularMatrixRankSequence F κ n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hmax := matrixMultiplication_rank_lower_max (K := F) hpos
      (rectangularMiddleDimension_pos κ hpos) hpos
      (rank_spec (matrixMultiplication (K := F) n (rectangularMiddleDimension κ n) n))
    have hnn : n * n ≤ rectangularMatrixRankSequence F κ n :=
      le_trans ((le_max_right _ _).trans (le_max_right _ _)) hmax
    simpa [pow_two] using hnn

/-- The standard flattening lower bound gives `2 ≤ ω(κ)` for every real `κ` over a field.
Note there is no hypothesis on `κ`: even for `κ < 0` the middle dimension is at least one for
positive `n`, so the outer flattening still has rank `n²`. -/
theorem two_le_rectangularMatrixMultiplicationExponent (κ : ℝ) :
    2 ≤ rectangularMatrixMultiplicationExponent F κ := by
  apply natCast_le_polynomialExponent
  · exact rectangularMatrixExponentLE_exists F κ
  · exact sq_le_rectangularMatrixRankSequence F κ

/-- Short-name form: `2 ≤ ω(κ)` over a field, for every real `κ`. -/
theorem two_le_rectangularOmega (κ : ℝ) : 2 ≤ rectangularOmega F κ :=
  two_le_rectangularMatrixMultiplicationExponent F κ

/-- The middle flattening gives `1 + κ ≤ ω(κ)` for every real `κ` over a field.  Together with
`two_le_rectangularOmega` this is the full conciseness lower bound `max 2 (1 + κ) ≤ ω(κ)`,
binding for `κ > 1`.

Proof sketch: for `n ≥ 1` we have `n^(1+κ) = n·n^κ ≤ n·⌈n^κ⌉`, and the `X`-leg flattening of
the concise tensor `⟨n, ⌈n^κ⌉, n⟩` bounds its rank below by `n·⌈n^κ⌉`; the real-exponent
lower-bound lemma for `polynomialExponent` converts this pointwise estimate into the bound on
the infimum. -/
theorem one_add_le_rectangularMatrixMultiplicationExponent (κ : ℝ) :
    1 + κ ≤ rectangularMatrixMultiplicationExponent F κ := by
  apply le_polynomialExponent_of_rpow_le
  · exact rectangularMatrixExponentLE_exists F κ
  · intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
    have hflat : n * rectangularMiddleDimension κ n ≤
        rectangularMatrixRankSequence F κ n :=
      mul_rectangularMiddleDimension_le_rectangularMatrixRankSequence F κ hn
    calc
      (n : ℝ) ^ (1 + κ) = (n : ℝ) * (n : ℝ) ^ κ := by
        rw [Real.rpow_add hnpos, Real.rpow_one]
      _ ≤ (n : ℝ) * (rectangularMiddleDimension κ n : ℝ) :=
        mul_le_mul_of_nonneg_left (rpow_le_rectangularMiddleDimension κ n) hnpos.le
      _ = ((n * rectangularMiddleDimension κ n : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (rectangularMatrixRankSequence F κ n : ℝ) := by exact_mod_cast hflat

/-- Short-name form: `1 + κ ≤ ω(κ)` over a field, for every real `κ`. -/
theorem one_add_le_rectangularOmega (κ : ℝ) : 1 + κ ≤ rectangularOmega F κ :=
  one_add_le_rectangularMatrixMultiplicationExponent F κ

/-- At `κ = 0` the rectangular exponent is exactly `2` over a field: `⟨n, 1, n⟩` is an outer
product, of rank exactly `n²` by the trivial decomposition and the outer flattening. -/
theorem rectangularMatrixMultiplicationExponent_zero :
    rectangularMatrixMultiplicationExponent F 0 = 2 := by
  apply le_antisymm
  · apply rectangularMatrixMultiplicationExponent_le
    apply PolynomialBound.of_le_pow _ 2
    intro n
    have h := rectangularMatrixRankSequence_le_mul F 0 n
    simpa [pow_two] using h
  · exact two_le_rectangularMatrixMultiplicationExponent F 0

/-- Short-name form: `ω(0) = 2` exactly, over a field. -/
theorem rectangularOmega_zero : rectangularOmega F 0 = 2 :=
  rectangularMatrixMultiplicationExponent_zero F

/-- Over a field, the region where the rectangular exponent is optimal is downward closed: if
`ω(κ₀) = 2` and `κ ≤ κ₀`, then `ω(κ) = 2`.

Proof sketch: monotonicity gives `ω(κ) ≤ ω(κ₀) = 2`, and the outer flattening of the concise
tensor gives `2 ≤ ω(κ)`. -/
theorem rectangularOmega_eq_two_of_le {κ κ₀ : ℝ} (hle : κ ≤ κ₀)
    (hbase : rectangularOmega F κ₀ = 2) :
    rectangularOmega F κ = 2 :=
  le_antisymm ((rectangularOmega_mono F hle).trans_eq hbase) (two_le_rectangularOmega F κ)

/-- If the square exponent is exactly `2`, then the rectangular exponent is exactly `2` at
every `κ ≤ 1`: monotonicity gives `ω(κ) ≤ ω(1) = ω = 2` and the flattening gives the reverse
inequality. -/
theorem rectangularOmega_eq_two_of_omega_eq_two {κ : ℝ} (h : omega F = 2)
    (hκ : κ ≤ 1) :
    rectangularOmega F κ = 2 :=
  rectangularOmega_eq_two_of_le F hκ ((rectangularOmega_one F).trans h)

/-- Any nonnegative `κ` with `ω(κ) = 2` satisfies `κ ≤ 1`, because `1 + κ ≤ ω(κ)`.  This is
the upper boundedness of the dual-exponent set. -/
theorem le_one_of_rectangularOmega_eq_two {κ : ℝ}
    (h : rectangularOmega F κ = 2) : κ ≤ 1 := by
  have hle := one_add_le_rectangularOmega F κ
  rw [h] at hle
  linarith

/-- The dual matrix-multiplication exponent `α` over `F`: the supremum of the nonnegative `κ`
whose rectangular exponent is exactly `2`.  Over a field the defining set contains `0`
(`rectangularOmega_zero`) and is bounded above by `1`
(`le_one_of_rectangularOmega_eq_two`), so the supremum is a well-behaved real number in
`[0, 1]`.

The supremum *is* attained: `RectangularInterpolation.rectangularOmega_rectangularAlpha` proves
`ω(α) = 2` from the convexity of `κ ↦ ω(κ)`, so `[0, α]` is a closed interval of optimality and
`α = 1` conversely forces `ω = 2`
(`RectangularInterpolation.omega_eq_two_of_rectangularAlpha_eq_one`).  Neither fact is available
in this module, which is upstream of convexity. -/
noncomputable def rectangularAlpha : ℝ :=
  sSup {κ : ℝ | 0 ≤ κ ∧ rectangularOmega F κ = 2}

/-- The dual-exponent set is bounded above by `1`. -/
theorem bddAbove_setOf_rectangularOmega_eq_two :
    BddAbove {κ : ℝ | 0 ≤ κ ∧ rectangularOmega F κ = 2} := by
  refine ⟨1, ?_⟩
  rintro κ ⟨-, hκ⟩
  exact le_one_of_rectangularOmega_eq_two F hκ

/-- The dual exponent is nonnegative: `κ = 0` belongs to the defining set. -/
theorem rectangularAlpha_nonneg : 0 ≤ rectangularAlpha F :=
  le_csSup (bddAbove_setOf_rectangularOmega_eq_two F)
    ⟨le_rfl, rectangularOmega_zero F⟩

/-- The dual exponent is at most one: every member of the defining set is at most `1`. -/
theorem rectangularAlpha_le_one : rectangularAlpha F ≤ 1 :=
  csSup_le ⟨0, le_rfl, rectangularOmega_zero F⟩
    fun _ hκ ↦ le_one_of_rectangularOmega_eq_two F hκ.2

/-- Over a field, `ω(κ) = 2` for every `κ` strictly below the dual exponent `α`.  Together with
`rectangularAlpha_le_one` this identifies `[0, α)` as a genuine interval of optimality, which is
the content that makes `rectangularAlpha` the right definition.

Proof sketch: `α` is the supremum of a nonempty set (it contains `0`), so `κ < α` yields a member
`κ₀` of that set with `κ < κ₀`; then `rectangularOmega_eq_two_of_le` applies.  Note that no
nonnegativity hypothesis on `κ` is needed: `2 ≤ ω(κ)` holds for every real `κ`. -/
theorem rectangularOmega_eq_two_of_lt_rectangularAlpha {κ : ℝ}
    (hκ : κ < rectangularAlpha F) :
    rectangularOmega F κ = 2 := by
  obtain ⟨κ₀, hmem, hlt⟩ :=
    exists_lt_of_lt_csSup (s := {κ : ℝ | 0 ≤ κ ∧ rectangularOmega F κ = 2})
      ⟨0, le_rfl, rectangularOmega_zero F⟩ hκ
  exact rectangularOmega_eq_two_of_le F hlt.le hmem.2

/-- If the square exponent is exactly `2`, the dual exponent is exactly `1`: the defining set
then contains `κ = 1` itself. -/
theorem rectangularAlpha_eq_one_of_omega_eq_two (h : omega F = 2) :
    rectangularAlpha F = 1 :=
  le_antisymm (rectangularAlpha_le_one F)
    (le_csSup (bddAbove_setOf_rectangularOmega_eq_two F)
      ⟨zero_le_one, rectangularOmega_eq_two_of_omega_eq_two F h le_rfl⟩)

end FieldLowerBound

end AlgebraicComplexity
