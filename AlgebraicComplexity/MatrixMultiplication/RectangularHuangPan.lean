/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RectangularInterpolation

/-!
# Huang--Pan's interpolation and blocking bounds for `ω(1, r, 1)`

Huang and Pan open §8.1 (*Fast rectangular matrix multiplication and applications*, J. Complexity
14 (1998), pp. 280--281) with two elementary upper bounds on the rectangular exponent, which they
use to extend their tables of `ω(1, r, 1)` from the finitely many `r` produced by their §6--§7
constructions to all real `r`.  Both are already proved in this repository under
Lotti--Romani-style names; this module restates them under the names, in the algebraic shape, and
with the section references of Huang--Pan, so that a reader following the paper finds them.

## Principal results

* `rectangularOmega_le_huangPan_interpolation`: the second branch of Huang--Pan (8.1),

  `ω(κ) ≤ (2(1 - κ) + (κ - κ₀)·ω) / (1 - κ₀)` for `κ₀ ≤ κ ≤ 1`, whenever `ω(κ₀) = 2`.

  This is `rectangularOmega_le_interpolation_of_eq_two`
  (`MatrixMultiplication/RectangularInterpolation.lean`) after
  the identity `2 + (ω - 2)(κ - κ₀)/(1 - κ₀) = (2(1 - κ) + (κ - κ₀)ω)/(1 - κ₀)`;
* `rectangularOmega_le_huangPan_blocking`: Huang--Pan's `g(r) = r - 1 + ω` for `r ≥ 1`.  This is
  `rectangularOmega_le_omega_add_sub_one` (`RectangularInterpolation.lean`) rewritten;
* `rectangularOmega_huangPan_eq_two`: the *first* branch of (8.1), `ω(r) = 2` for `0 ≤ r ≤ α`.
  Over a field this needs the attainment `ω(α) = 2`
  (`rectangularOmega_rectangularAlpha`), so the closed endpoint `r = α` is included;
* `rectangularOmega_le_huangPan_interpolation_alpha`: the second branch at the classical witness
  `κ₀ = α`;
* the crossing-point algebra of §8.1: `huangPan_interpolation_sub_blocking` computes the exact
  difference of the two bounding expressions, `huangPan_interpolation_eq_blocking_one` shows they
  agree at `κ = 1`, and `huangPan_blocking_le_interpolation_of_le_one` /
  `huangPan_interpolation_le_blocking_of_one_le` say which one is smaller on which side of `1`.

## Non-goals

Huang--Pan's numerical crossing point `r ≈ 1.171` of §8.1 compares their *own* §6--§7 bounds with
`g(r) = r - 1 + ω`.  Those bounds have since landed, but in the client layer, which this core
module must not import: (6.1) is `Examples.huangPan_rectangularOmega_le_of_one_le_sharp`
(`Examples/CoppersmithWinogradEasyRectangularSharpBound.lean`) and §7's `f(r)` is
`Examples.huangPan_fullTensor_rectangularOmega_le`, with its `r ≤ 1` companion
`Examples.huangPan_fullTensor_rectangularOmega_le_of_le_one`
(`Examples/CoppersmithWinogradRectangularHuangPan.lean`).

The crossing-point comparison is therefore now a *client-side* statement, and only half of it is
cheap.  At a fixed rational `r` and field size `q` the value of `f(r)` is a closed
rational-logarithm expression, so comparing it with a *given* number is the numeric-certificate
exercise that `Analysis/LogConstants.lean` exists for.  Comparing it with `g(r) = r - 1 + ω`
is not, because `g` mentions `ω` itself, of which this tree deliberately assumes no numeric
value; the crossing point `r ≈ 1.171` is a consequence of `ω ≈ 2.373`, which is an input to
Huang--Pan's table and not a theorem here.  Neither comparison is proved in this module.

What is available here is the exact comparison of the two elementary bounds of (8.1), which meet
at `r = 1` and
whose relative order on either side is governed by the sign of `(1 - κ₀) - (ω - 2)`, i.e. by
whether `ω + κ₀ ≤ 3`.  The corollary
`huangPan_interpolation_le_blocking_of_omega_le` records the regime `ω ≤ 2.373`, `α ≤ 0.6`, in
which the interpolation expression is the smaller of the two beyond `r = 1`; no unproven numeric
value of `ω` or `α` is assumed anywhere, the numbers appear only as hypotheses.

## References

* X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity 14 (1998), 257--299; §8.1, pp. 280--281, formula (8.1) and the function
  `g(r) = r - 1 + ω`.
* G. Lotti and F. Romani, *On the asymptotic complexity of rectangular matrix multiplication*,
  Theoret. Comput. Sci. 23 (1983), for the interpolation formula itself.
* D. Coppersmith, *Rapid multiplication of rectangular matrices*, SIAM J. Comput. 11 (1982),
  for the source of a nonzero `α`.
-/

namespace AlgebraicComplexity

open Tensor Growth

universe u

variable (K : Type u) [CommSemiring K]

/-! ## The two bounds of Huang--Pan (8.1) -/

/-- **Huang--Pan (8.1), second branch** (§8.1, p. 280).  If some `κ₀ ∈ [0, 1)` already has
`ω(κ₀) = 2`, then for every `κ₀ ≤ κ ≤ 1`

`ω(κ) ≤ (2·(1 - κ) + (κ - κ₀)·ω) / (1 - κ₀)`.

This is the Lotti--Romani interpolation bound of
`rectangularOmega_le_interpolation_of_eq_two` written in Huang--Pan's normalized form: the two
right-hand sides `2 + (ω - 2)·(κ - κ₀)/(1 - κ₀)` and `(2(1 - κ) + (κ - κ₀)ω)/(1 - κ₀)` are equal
as real numbers, since `2(1 - κ₀) + (ω - 2)(κ - κ₀) = 2(1 - κ) + (κ - κ₀)ω`.  Like its source it
holds over every commutative semiring. -/
theorem rectangularOmega_le_huangPan_interpolation {κ κ₀ : ℝ}
    (hκ₀ : 0 ≤ κ₀) (h1 : κ₀ < 1) (hb : rectangularOmega K κ₀ = 2)
    (h : κ₀ ≤ κ) (h' : κ ≤ 1) :
    rectangularOmega K κ ≤ (2 * (1 - κ) + (κ - κ₀) * omega K) / (1 - κ₀) := by
  have hden : (0 : ℝ) < 1 - κ₀ := by linarith
  have hle := rectangularOmega_le_interpolation_of_eq_two K hκ₀ h1 hb h h'
  have hEq : 2 + (omega K - 2) * (κ - κ₀) / (1 - κ₀) =
      (2 * (1 - κ) + (κ - κ₀) * omega K) / (1 - κ₀) := by
    field_simp
    ring
  rwa [hEq] at hle

/-- **Huang--Pan's `g(r) = r - 1 + ω`** (§8.1, p. 281).  For `r ≥ 1`,

`ω(r) ≤ r - 1 + ω`,

obtained by cutting the `n × n^r` by `n^r × n` product into `n^(r-1)` square products of side
`n`.  This is `rectangularOmega_le_omega_add_sub_one` with the summands reordered; it holds over
every commutative semiring. -/
theorem rectangularOmega_le_huangPan_blocking {r : ℝ} (hr : 1 ≤ r) :
    rectangularOmega K r ≤ r - 1 + omega K := by
  have h := rectangularOmega_le_omega_add_sub_one K hr
  linarith

/-! ## The two bounds at the dual exponent `α`, over a field -/

section Field

variable (F : Type u) [Field F]

/-- **Huang--Pan (8.1), first branch** (§8.1, p. 280): `ω(r) = 2` for every `0 ≤ r ≤ α`.

The interval is *closed* at `α`, because over a field the supremum defining `α` is attained
(`rectangularOmega_rectangularAlpha`); the strict form `r < α` is
`rectangularOmega_eq_two_of_lt_rectangularAlpha` in
`MatrixMultiplication/RectangularExponent.lean`. -/
theorem rectangularOmega_huangPan_eq_two {r : ℝ} (hr : r ≤ rectangularAlpha F) :
    rectangularOmega F r = 2 :=
  rectangularOmega_eq_two_of_le F hr (rectangularOmega_rectangularAlpha F)

/-- **Huang--Pan (8.1), second branch at the classical witness `κ₀ = α`.**  Over a field with
`α < 1`, for every `α ≤ κ ≤ 1`

`ω(κ) ≤ (2·(1 - κ) + (κ - α)·ω) / (1 - α)`.

Together with `rectangularOmega_huangPan_eq_two` below `α` and
`rectangularOmega_le_huangPan_blocking` above `1`, this covers every `r ≥ 0`. -/
theorem rectangularOmega_le_huangPan_interpolation_alpha
    (hα : rectangularAlpha F < 1) {κ : ℝ}
    (h : rectangularAlpha F ≤ κ) (h' : κ ≤ 1) :
    rectangularOmega F κ ≤
      (2 * (1 - κ) + (κ - rectangularAlpha F) * omega F) / (1 - rectangularAlpha F) :=
  rectangularOmega_le_huangPan_interpolation F (rectangularAlpha_nonneg F) hα
    (rectangularOmega_rectangularAlpha F) h h'

end Field

/-! ## The crossing-point algebra of §8.1

Huang--Pan compare their bounds as functions of `r` and read off where one overtakes the other.
The three lemmas below do that for the two bounds of (8.1) themselves.  They are statements about
real numbers only: `w` stands for `ω` and `κ₀` for the witness exponent, and no
matrix-multiplication content is involved. -/

/-- The exact difference of the two bounding expressions of (8.1).  Writing
`h(κ) = (2(1 - κ) + (κ - κ₀)w)/(1 - κ₀)` for the interpolation expression and
`g(κ) = κ - 1 + w` for the blocking expression,

`h(κ) - g(κ) = (1 - κ)·((1 - κ₀) - (w - 2)) / (1 - κ₀)`.

Both factors of the numerator change sign at a single point, which is why the two bounds cross
exactly once (at `κ = 1`) unless `(1 - κ₀) = w - 2`, in which case they coincide identically. -/
theorem huangPan_interpolation_sub_blocking {κ κ₀ w : ℝ} (h1 : κ₀ < 1) :
    (2 * (1 - κ) + (κ - κ₀) * w) / (1 - κ₀) - (κ - 1 + w) =
      (1 - κ) * ((1 - κ₀) - (w - 2)) / (1 - κ₀) := by
  have hden : (1 : ℝ) - κ₀ ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- The two bounds of (8.1) meet at `κ = 1`, where both equal `ω`: the interpolation branch is
tight exactly at the square case, which is the reason Huang--Pan can splice them into one
piecewise bound. -/
theorem huangPan_interpolation_eq_blocking_one {κ₀ w : ℝ} (h1 : κ₀ < 1) :
    (2 * (1 - (1 : ℝ)) + ((1 : ℝ) - κ₀) * w) / (1 - κ₀) = (1 : ℝ) - 1 + w := by
  have hden : (1 : ℝ) - κ₀ ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- Below the crossing point, i.e. for `κ ≤ 1`, the *blocking* expression is the smaller of the
two, provided `w - 2 ≤ 1 - κ₀` (equivalently `w + κ₀ ≤ 3`).  It is nevertheless useless there:
`rectangularOmega_le_huangPan_blocking` requires `κ ≥ 1`, and indeed at `κ = 0` the blocking
expression `ω - 1` is below the true value `ω(0) = 2`.  The lemma is recorded to make the sign
analysis of §8.1 explicit. -/
theorem huangPan_blocking_le_interpolation_of_le_one {κ κ₀ w : ℝ}
    (h1 : κ₀ < 1) (hw : w - 2 ≤ 1 - κ₀) (hκ : κ ≤ 1) :
    κ - 1 + w ≤ (2 * (1 - κ) + (κ - κ₀) * w) / (1 - κ₀) := by
  have hden : (0 : ℝ) < 1 - κ₀ := by linarith
  have hdiff := huangPan_interpolation_sub_blocking (κ := κ) (κ₀ := κ₀) (w := w) h1
  have hnonneg : 0 ≤ (1 - κ) * ((1 - κ₀) - (w - 2)) / (1 - κ₀) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hden.le
  linarith

/-- Above the crossing point, i.e. for `κ ≥ 1`, the *interpolation* expression is the smaller of
the two, provided `w - 2 ≤ 1 - κ₀`.  It is again unavailable there — the interpolation bound is
proved only for `κ ≤ 1` — so the two bounds of (8.1) are each optimal exactly on their own side
of `κ = 1`, which is what makes the piecewise bound of §8.1 the best consequence of the pair. -/
theorem huangPan_interpolation_le_blocking_of_one_le {κ κ₀ w : ℝ}
    (h1 : κ₀ < 1) (hw : w - 2 ≤ 1 - κ₀) (hκ : 1 ≤ κ) :
    (2 * (1 - κ) + (κ - κ₀) * w) / (1 - κ₀) ≤ κ - 1 + w := by
  have hden : (0 : ℝ) < 1 - κ₀ := by linarith
  have hdiff := huangPan_interpolation_sub_blocking (κ := κ) (κ₀ := κ₀) (w := w) h1
  have hnonpos : (1 - κ) * ((1 - κ₀) - (w - 2)) / (1 - κ₀) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)) hden.le
  linarith

/-- The regime of Huang--Pan's tables, stated without assuming any unproved numeric value: if the
square exponent is at most `2.373` and the witness exponent is at most `0.6`, then the hypothesis
`w - 2 ≤ 1 - κ₀` of the two comparison lemmas holds, so beyond `κ = 1` the interpolation
expression is the smaller of the two.  With the currently known `ω < 2.3729` and `α < 0.322` both
numeric hypotheses are satisfied. -/
theorem huangPan_interpolation_le_blocking_of_omega_le {κ κ₀ w : ℝ}
    (hw : w ≤ 2.373) (hκ₀ : κ₀ ≤ 0.6) (hκ : 1 ≤ κ) :
    (2 * (1 - κ) + (κ - κ₀) * w) / (1 - κ₀) ≤ κ - 1 + w := by
  refine huangPan_interpolation_le_blocking_of_one_le (by linarith) ?_ hκ
  linarith

end AlgebraicComplexity
