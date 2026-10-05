/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RectangularExponent

/-!
# From a family of rectangular certificates to a rectangular exponent bound

`MatrixMultiplication/RectangularExponent.lean` defines `ω(κ) = rectangularOmega K κ` as an
infimum of admissible polynomial exponents for the rank sequence
`n ↦ rank ⟨n, ⌈n^κ⌉, n⟩`, but the only way it offers to *produce* an admissible exponent is the
elementary `n·⌈n^κ⌉·n` decomposition.  A construction — Coppersmith 1982, Coppersmith 1997,
Huang--Pan 1998 — instead delivers a sparse family of explicit certificates

`RankLE (r s) ⟨A s, C s, A s⟩`

whose dimensions grow geometrically, and whose middle dimension is at least `(A s)^κ`.  This
module is the adapter between the two, the rectangular analogue of
`MatrixMultiplication/BiniInterpolation.lean` for the square exponent.

## Principal results

* `rectangularMatrixExponentLE_of_certificates`: a family of rank certificates with
  `(A s)^κ ≤ C s` whose sizes are covered by `D·n^τ` at every scale gives
  `RectangularMatrixExponentLE K κ τ`, hence `ω(κ) ≤ τ` (`rectangularOmega_le_of_certificates`).
  Two roundings are absorbed for free: `C s ≥ (A s)^κ ≥ n^κ` upgrades to `C s ≥ ⌈n^κ⌉₊` because
  `C s` is a natural number, and the outer dimension only has to *dominate* `n`, since
  `matrixMultiplication_restricts` cuts a larger product down to a smaller one;
* `rectangularMatrixRankSequence_eq_rank_outer`: the same rank sequence read in Huang--Pan's
  outer-dimension normalization, `rank ⟨n, ⌈n^κ⌉, n⟩ = rank ⟨n, n, ⌈n^κ⌉⟩`, so that
  `rectangularOmega K κ` is on record as `ω(1, 1, κ)` as well as `ω(1, κ, 1)`;
* `rectangularMatrixExponentLE_two_add_of_certificates`: the sanity client.  The elementary bound
  `ω(κ) ≤ 2 + κ` is re-derived from the packager alone, exercising every hypothesis: the
  certificate family is the trivial decomposition of `⟨s, ⌈s^κ⌉, s⟩`, the middle-dimension
  hypothesis is `Nat.le_ceil`, and the covering constant is `D = 2`, the factor lost to rounding.

## Design notes

The hypotheses are stated exactly as `Growth.PolynomialBound` consumes them, which is why `τ ≥ 0`
appears as an explicit hypothesis rather than a conclusion: over a general commutative semiring
there is no lower bound on the rank of a matrix-multiplication tensor, so nonnegativity of the
exponent cannot be recovered from the certificates.  Over a field it is automatic, but requiring
it costs a client nothing.

The covering hypothesis is a genuine `∀ n ≥ 1` statement rather than an eventual one because
`PolynomialBound` quantifies over all positive `n`; a client whose family only covers large `n`
should absorb the finitely many small scales into the constant `D` before applying the packager,
or route through `Growth.PolynomialBound` directly.

The certificate shape is `⟨A s, C s, A s⟩` — the middle dimension is the large one — matching
`rectangularMatrixRankSequence`.  A construction that produces `⟨A s, A s, C s⟩` instead should
rotate it with `Tensor.RankLE.matrixMultiplication_cycle` first;
`rectangularMatrixRankSequence_eq_rank_outer` records that the two normalizations agree.

## References

* D. Coppersmith, *Rapid multiplication of rectangular matrices*, SIAM J. Comput. 11 (1982).
* X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity 14 (1998); the exponent `ω(1, 1, r)` of §1 is the `rectangularOmega` of this
  repository, by `rectangularMatrixRankSequence_eq_rank_outer`.
-/

namespace AlgebraicComplexity

open Tensor Growth

universe u

variable (K : Type u) [CommSemiring K]

/-! ## The packager -/

/-- **From explicit rectangular certificates to an admissible rectangular exponent.**

Suppose that for every index `s` there is a rank-`r s` algorithm for the rectangular product
`⟨A s, C s, A s⟩` whose middle dimension satisfies `(A s)^κ ≤ C s`, and that every scale `n ≥ 1`
is covered by some index `s` with `n ≤ A s` and `r s ≤ D·n^τ`.  Then `τ` is an admissible
polynomial exponent for the `κ`-rectangular rank sequence.

Proof sketch: fix `n ≥ 1` and take a covering index `s`.  From `n ≤ A s` and `κ ≥ 0` we get
`n^κ ≤ (A s)^κ ≤ C s`, and since `C s` is a natural number this is exactly
`⌈n^κ⌉₊ ≤ C s`.  So `⟨n, ⌈n^κ⌉, n⟩` is a restriction of `⟨A s, C s, A s⟩` in all three
dimensions (`matrixMultiplication_restricts`), whence
`rank ⟨n, ⌈n^κ⌉, n⟩ ≤ rank ⟨A s, C s, A s⟩ ≤ r s ≤ D·n^τ`.  The single constant `D` therefore
witnesses the polynomial bound. -/
theorem rectangularMatrixExponentLE_of_certificates {κ τ : ℝ} (hκ : 0 ≤ κ) (hτ : 0 ≤ τ)
    {A C r : ℕ → ℕ} {D : ℝ} (hD : 0 < D)
    (hcert : ∀ s, RankLE (r s) (matrixMultiplication (K := K) (A s) (C s) (A s)))
    (hmid : ∀ s, ((A s : ℝ)) ^ κ ≤ (C s : ℝ))
    (hcover : ∀ n : ℕ, 1 ≤ n → ∃ s, n ≤ A s ∧ (r s : ℝ) ≤ D * (n : ℝ) ^ τ) :
    RectangularMatrixExponentLE K κ τ := by
  refine ⟨hτ, D, hD, ?_⟩
  intro n hn
  obtain ⟨s, hnA, hrs⟩ := hcover n hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnA' : (n : ℝ) ≤ (A s : ℝ) := by exact_mod_cast hnA
  have hmidn : ((n : ℝ)) ^ κ ≤ (C s : ℝ) :=
    le_trans (Real.rpow_le_rpow hn0 hnA' hκ) (hmid s)
  have hceil : rectangularMiddleDimension κ n ≤ C s := Nat.ceil_le.mpr hmidn
  have hres :
      Restricts (matrixMultiplication (K := K) (A s) (C s) (A s))
        (matrixMultiplication (K := K) n (rectangularMiddleDimension κ n) n) :=
    matrixMultiplication_restricts hnA hceil hnA
  have hrank : rectangularMatrixRankSequence K κ n ≤ r s :=
    le_trans (rank_restricts_le hres) (rank_le_iff.mpr (hcert s))
  calc
    (rectangularMatrixRankSequence K κ n : ℝ) ≤ (r s : ℝ) := by exact_mod_cast hrank
    _ ≤ D * (n : ℝ) ^ τ := hrs

/-- Exponent-level form of the packager: a covered family of rectangular rank certificates bounds
the rectangular exponent, `ω(κ) ≤ τ`. -/
theorem rectangularOmega_le_of_certificates {κ τ : ℝ} (hκ : 0 ≤ κ) (hτ : 0 ≤ τ)
    {A C r : ℕ → ℕ} {D : ℝ} (hD : 0 < D)
    (hcert : ∀ s, RankLE (r s) (matrixMultiplication (K := K) (A s) (C s) (A s)))
    (hmid : ∀ s, ((A s : ℝ)) ^ κ ≤ (C s : ℝ))
    (hcover : ∀ n : ℕ, 1 ≤ n → ∃ s, n ≤ A s ∧ (r s : ℝ) ≤ D * (n : ℝ) ^ τ) :
    rectangularOmega K κ ≤ τ :=
  rectangularOmega_le K
    (rectangularMatrixExponentLE_of_certificates K hκ hτ hD hcert hmid hcover)

/-! ## The outer-dimension normalization `ω(1, 1, κ)` -/

/-- The rectangular rank sequence in Huang--Pan's normalization: the rank of `⟨n, ⌈n^κ⌉, n⟩`,
which is what `rectangularMatrixRankSequence` measures, equals the rank of `⟨n, n, ⌈n^κ⌉⟩`.

Consequently `rectangularOmega K κ` is simultaneously the exponent written `ω(1, κ, 1)` in the
Lotti--Romani normalization used by `RectangularExponent.lean` and the exponent written
`ω(1, 1, κ)` by Huang--Pan, and no translation is needed when reading their statements.

Proof sketch: the cyclic symmetry of matrix multiplication rotates `⟨m,n,p⟩` to `⟨p,m,n⟩` while
preserving rank certificates, and one rotation carries `⟨n, ⌈n^κ⌉, n⟩` to `⟨n, n, ⌈n^κ⌉⟩` while
two more carry it back, so the two ranks bound each other. -/
theorem rectangularMatrixRankSequence_eq_rank_outer (κ : ℝ) (n : ℕ) :
    rectangularMatrixRankSequence K κ n =
      rank (matrixMultiplication (K := K) n n (rectangularMiddleDimension κ n)) := by
  set M := rectangularMiddleDimension κ n with hM
  unfold rectangularMatrixRankSequence
  refine le_antisymm ?_ ?_
  · -- `⟨n, n, M⟩` rotates twice to `⟨n, M, n⟩`.
    refine rank_le_iff.mpr ?_
    exact (rank_spec (matrixMultiplication (K := K) n n M)).matrixMultiplication_cycle
      |>.matrixMultiplication_cycle
  · -- `⟨n, M, n⟩` rotates once to `⟨n, n, M⟩`.
    exact rank_le_iff.mpr
      (rank_spec (matrixMultiplication (K := K) n M n)).matrixMultiplication_cycle

/-! ## Sanity client: the elementary bound through the packager -/

/-- **Sanity client.**  The elementary bound `ω(κ) ≤ 2 + κ` for `κ ≥ 0`, obtained from
`rectangularMatrixExponentLE_of_certificates` alone.

The certificate family is the trivial `A s · C s · A s`-term decomposition of
`⟨s, ⌈s^κ⌉, s⟩`, the middle-dimension hypothesis is `Nat.le_ceil`, and each scale `n` is covered
by the index `s = n` with constant `D = 2` — the factor of two being exactly what rounding the
middle dimension up costs, by `rectangularMiddleDimension_le_two_mul_rpow`.

This re-proves `rectangularMatrixExponentLE_two_add` of `RectangularExponent.lean` and exists to
demonstrate that the packager's hypothesis shape is usable by a real client; the two proofs are
independent. -/
theorem rectangularMatrixExponentLE_two_add_of_certificates {κ : ℝ} (hκ : 0 ≤ κ) :
    RectangularMatrixExponentLE K κ (2 + κ) := by
  refine rectangularMatrixExponentLE_of_certificates K hκ (by linarith)
    (A := fun s ↦ s) (C := fun s ↦ rectangularMiddleDimension κ s)
    (r := fun s ↦ s * rectangularMiddleDimension κ s * s) (D := 2) two_pos
    (fun s ↦ matrixMultiplication_rankLE (K := K) s (rectangularMiddleDimension κ s) s)
    (fun s ↦ rpow_le_rectangularMiddleDimension κ s) ?_
  intro n hn
  refine ⟨n, le_rfl, ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  have hmid : (rectangularMiddleDimension κ n : ℝ) ≤ 2 * (n : ℝ) ^ κ :=
    rectangularMiddleDimension_le_two_mul_rpow hκ hn
  have hsq : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) * (n : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  calc
    ((n * rectangularMiddleDimension κ n * n : ℕ) : ℝ)
        = (n : ℝ) * (rectangularMiddleDimension κ n : ℝ) * (n : ℝ) := by
          push_cast
          ring
    _ ≤ (n : ℝ) * (2 * (n : ℝ) ^ κ) * (n : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hnpos.le
          exact mul_le_mul_of_nonneg_left hmid hnpos.le
    _ = 2 * ((n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ κ) := by
          rw [hsq]
          ring
    _ = 2 * (n : ℝ) ^ (2 + κ) := by
          rw [← Real.rpow_add hnpos]

/-- Exponent-level form of the sanity client: `ω(κ) ≤ 2 + κ` for `κ ≥ 0`, through the
packager. -/
theorem rectangularOmega_le_two_add_of_certificates {κ : ℝ} (hκ : 0 ≤ κ) :
    rectangularOmega K κ ≤ 2 + κ :=
  rectangularOmega_le K (rectangularMatrixExponentLE_two_add_of_certificates K hκ)

end AlgebraicComplexity
