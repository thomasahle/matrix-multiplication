/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.IndependenceBarrier
import AlgebraicComplexity.MatrixMultiplication.IndependenceMassDistribution

/-!
# From a corner configuration to an exponent barrier

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module joins the two halves of the
Galactic barrier program of

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671v1,

namely **Corollary 5.1** (`MatrixMultiplication/IndependenceMassDistribution.lean`: a table with
two corner terms has `Ī(T) ≤ cornerBound Q < Q`) and **Theorem 4.1 / Corollary 4.3**
(`MatrixMultiplication/IndependenceBarrier.lean`: `Ī(T) ≤ R̃(T)^s` with `s < 1` forces
`ω_g^{coord}(T) ≥ 6/(s+2) > 2`).  Neither of those two files imports the other, and every client
that owns a corner configuration needs exactly the same three-step chain:

```text
Ī(T) ≤ cornerBound Q   →   Ī(T) ≤ R̃(T)^{1 − cornerExponent Q}
                       →   6/(3 − cornerExponent Q) ≤ ω_g^{coord}(T)
                       →   2 < ω_g^{coord}(T).
```

The three steps are `asymptoticIndependenceNumber_le_rpow_asymptoticRank_of_le_cornerBound`,
`six_div_sub_cornerExponent_le_coordinateGalacticExponent_of_concise` and
`two_lt_six_div_sub_cornerExponent`.  The only client-supplied data are the corner bound itself,
conciseness of the coefficient table, the leg-dimension bound `Q ≤ R̃(T)`, and nonemptiness of the
certificate value set; `Examples/LowerTriangularBarrier.lean` (Theorem 7.5) and
`Examples/GeneralizedCoppersmithWinogradBarrier.lean` (Lemma 7.1) are the two current instances.

`Q` is the number of variables per leg in Corollary 5.1, so the constant
`c_Q = 6/(3 − cornerExponent Q)` degrades as `Q` grows: this route gives a barrier for each fixed
`Q`, not a universal one.

## The chain is parametric in the exponent gap

Nothing in the three steps uses the corner configuration, or even the *value* of
`cornerExponent Q`: all that is consumed is a *gap* `g ≤ 1` in an absolute bound
`Ī(T) ≤ Q^{1 − g}`.  The chain is therefore stated first in that generality —
`asymptoticIndependenceNumber_le_rpow_asymptoticRank_of_le_rpow_card`,
`six_div_sub_le_coordinateGalacticExponent_of_le_rpow_card` and `two_lt_six_div_sub` — and the
corner statements above are its `g = cornerExponent Q` specializations.  The second source of a
gap in this repository is AVW Theorem 7.6 (`Examples/LowerTriangularDiagonal.lean`), which supplies
`g = diagonalExponent Q` for a lower triangular table whose diagonal misses a `z`-variable.

## References

* J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
  Matrix Multiplication*, arXiv:1810.08671v1, Corollary 5.1 and Theorem 4.1 / Corollary 4.3.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

/-- **An exponent gap in `(0, 1]` gives a constant above `2`.**  For `0 < g ≤ 1` one has
`3 − g ∈ [2, 3)`, hence `6/(3 − g) > 2`.

This is the `s = 1 − g` case of `two_lt_six_div_add_two`, written in the *gap* form in which the
clients of this module state their conclusion.  `g` is the saving over the trivial bound
`Ī(T) ≤ Q`: the corner configuration of AVW Corollary 5.1 supplies `g = cornerExponent Q`, and the
lower triangular criterion of AVW Theorem 7.6 supplies `g = diagonalExponent Q`. -/
theorem two_lt_six_div_sub {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1) : 2 < 6 / (3 - g) := by
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- **The corner constant is above `2`.**  For every `Q ≥ 2` the exponent gap `cornerExponent Q`
lies in `(0, 1]`, so `3 − cornerExponent Q ∈ [2, 3)` and `6/(3 − cornerExponent Q) > 2`.

This is the `g = cornerExponent Q` case of `two_lt_six_div_sub`. -/
theorem two_lt_six_div_sub_cornerExponent {Q : ℕ} (hQ : 2 ≤ Q) :
    2 < 6 / (3 - cornerExponent Q) :=
  two_lt_six_div_sub (cornerExponent_pos hQ) (cornerExponent_le_one hQ)

section Rpow

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] {T : (∀ i, κ i) → K}

omit [∀ i, DecidableEq (κ i)] in
/-- **A saving over the trivial bound, in the shape Corollary 4.3 consumes.**  An absolute bound
`Ī(T) ≤ Q^{1 − g}` with gap `g ≤ 1` becomes the relative bound `Ī(T) ≤ R̃(T)^{1 − g}` as soon as
the asymptotic rank is at least `Q`, which for a concise table is the leg-dimension count.

Proof sketch: the exponent `1 − g` is nonnegative, and `x ↦ x^{1-g}` is monotone. -/
theorem asymptoticIndependenceNumber_le_rpow_asymptoticRank_of_le_rpow_card {Q : ℕ} {g : ℝ}
    (hg1 : g ≤ 1) (hcard : ((Q : ℕ) : ℝ) ≤ Tensor.asymptoticRank (coordinateTensor T))
    (hI : asymptoticIndependenceNumber T ≤ (Q : ℝ) ^ (1 - g)) :
    asymptoticIndependenceNumber T ≤
      Tensor.asymptoticRank (coordinateTensor T) ^ (1 - g) :=
  hI.trans (Real.rpow_le_rpow (by positivity) hcard (by linarith))

omit [∀ i, DecidableEq (κ i)] in
/-- **Corollary 5.1 in the shape Corollary 4.3 consumes.**  A corner bound `Ī(T) ≤ cornerBound Q`
becomes the relative bound `Ī(T) ≤ R̃(T)^{1 − cornerExponent Q}` as soon as the asymptotic rank is
at least `Q`, which for a concise table is the leg-dimension count.

This is the `g = cornerExponent Q` case of
`asymptoticIndependenceNumber_le_rpow_asymptoticRank_of_le_rpow_card`, since
`cornerBound Q = Q^{1 − cornerExponent Q}` by definition and `cornerExponent Q ≤ 1`
(`cornerExponent_le_one`). -/
theorem asymptoticIndependenceNumber_le_rpow_asymptoticRank_of_le_cornerBound {Q : ℕ}
    (hQ : 2 ≤ Q) (hcard : ((Q : ℕ) : ℝ) ≤ Tensor.asymptoticRank (coordinateTensor T))
    (hI : asymptoticIndependenceNumber T ≤ cornerBound Q) :
    asymptoticIndependenceNumber T ≤
      Tensor.asymptoticRank (coordinateTensor T) ^ (1 - cornerExponent Q) :=
  asymptoticIndependenceNumber_le_rpow_asymptoticRank_of_le_rpow_card
    (cornerExponent_le_one hQ) hcard hI

end Rpow

section Barrier

variable (K : Type u) [Field K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [∀ i, Nonempty (κ i)]
variable {T : (∀ i, κ i) → K}

/-- **The barrier chain, for an arbitrary exponent gap.**  A concise coefficient table with
`Q ≤ R̃(T)` and `2 ≤ Q` whose asymptotic independence number satisfies `Ī(T) ≤ Q^{1 − g}` for some
gap `g ≤ 1` admits no Galactic exponent below `6/(3 − g)`; for `g > 0` that constant is strictly
above `2` (`two_lt_six_div_sub`).

`g` is any saving over the trivial bound `Ī(T) ≤ Q`.  The two current sources of such a saving in
this repository are AVW Corollary 5.1 (`g = cornerExponent Q`, from a corner configuration) and
AVW Theorem 7.6 (`g = diagonalExponent Q`, from a lower triangular table whose diagonal misses a
`z`-variable); nothing in the chain depends on which.

Proof sketch: `asymptoticIndependenceNumber_le_rpow_asymptoticRank_of_le_rpow_card` puts the bound
in the form `Ī(T) ≤ R̃(T)^s` with `s = 1 − g`, and AVW Corollary 4.3
(`six_div_add_two_le_coordinateGalacticExponent_of_concise`) concludes; `1 < R̃(T)` comes from
`2 ≤ Q ≤ R̃(T)`. -/
theorem six_div_sub_le_coordinateGalacticExponent_of_le_rpow_card {Q : ℕ} {g : ℝ}
    (hQ : 2 ≤ Q) (hg1 : g ≤ 1) (hconc : ∀ i, Tensor.IsCoordinateConcise T i)
    (hcard : ((Q : ℕ) : ℝ) ≤ Tensor.asymptoticRank (coordinateTensor T))
    (hI : asymptoticIndependenceNumber T ≤ (Q : ℝ) ^ (1 - g))
    (hne : (coordinateGalacticValues K T).Nonempty) :
    6 / (3 - g) ≤ coordinateGalacticExponent K T := by
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hR : 1 < Tensor.asymptoticRank (coordinateTensor T) := by linarith
  have hs2 : (0 : ℝ) < 1 - g + 2 := by linarith
  have hmain := six_div_add_two_le_coordinateGalacticExponent_of_concise K
    (s := 1 - g) hconc hR hs2
    (asymptoticIndependenceNumber_le_rpow_asymptoticRank_of_le_rpow_card hg1 hcard hI) hne
  rwa [show 1 - g + 2 = 3 - g by ring] at hmain

/-- **The corner barrier.**  A concise coefficient table with `Q ≥ 2` variables per leg (more
precisely, with `Q ≤ R̃(T)`) whose asymptotic independence number obeys the corner bound of AVW
Corollary 5.1 admits no Galactic exponent below the explicit constant

```text
c_Q = 6 / (3 − cornerExponent Q),     cornerExponent Q = 1/(Q² (Q+1)² log Q).
```

This is the `g = cornerExponent Q` case of
`six_div_sub_le_coordinateGalacticExponent_of_le_rpow_card`, since
`cornerBound Q = Q^{1 − cornerExponent Q}` by definition. -/
theorem six_div_sub_cornerExponent_le_coordinateGalacticExponent_of_concise {Q : ℕ}
    (hQ : 2 ≤ Q) (hconc : ∀ i, Tensor.IsCoordinateConcise T i)
    (hcard : ((Q : ℕ) : ℝ) ≤ Tensor.asymptoticRank (coordinateTensor T))
    (hI : asymptoticIndependenceNumber T ≤ cornerBound Q)
    (hne : (coordinateGalacticValues K T).Nonempty) :
    6 / (3 - cornerExponent Q) ≤ coordinateGalacticExponent K T :=
  six_div_sub_le_coordinateGalacticExponent_of_le_rpow_card K hQ (cornerExponent_le_one hQ)
    hconc hcard hI hne

end Barrier

end AlgebraicComplexity
