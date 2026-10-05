/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordQuotient

/-!
# Additive-hashing obstruction for the sorted-pair quotient

Pair sorting is a sound tensor coarsening, but it is not a tight-support labeling.  Sorting each
leg independently can destroy the coordinatewise CW sum equation.  More intrinsically, six
coarse support relations force every additive legal labeling to identify the two distinct
weight-two symbols `02` and `11` on the `X` leg (and cyclically on the other legs) whenever two
is nonzero.

Consequently total-weight hashing cannot be silently upgraded to injectivity of full sorted-pair
labels, and flattening the two sorted digits is not a legal replacement.  Any proof using the
physical three-leg quotient must either use a non-additive extraction theorem, retain additional
orientation data, or account for an explicit selection loss.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-- A concrete pair of coordinatewise legal raw CW triples becomes non-legal after sorting each
leg independently. -/
theorem cwSortedPairSplitWord_not_coordinatewise_legal :
    let x := cwSplitPair (0 : SplitDigit) 2
    let y := cwSplitPair (2 : SplitDigit) 0
    let z := cwSplitPair (0 : SplitDigit) 0
    (∀ position, (x position : ℕ) + (y position : ℕ) + (z position : ℕ) = 2) ∧
      ¬ ∀ position,
        (cwSortedPairSplitWord x position : ℕ) +
          (cwSortedPairSplitWord y position : ℕ) +
          (cwSortedPairSplitWord z position : ℕ) = 2 := by
  decide

/-- The six displayed sorted-pair support relations force the additive `X` labels of `02` and
`11` to coincide.  This is the algebraic core of the tightness obstruction; it works over every
field in which two is nonzero and therefore applies to the affine prime fields used for hashing.
-/
theorem six_sortedPair_relations_force_X02_eq_X11
    {R : Type*} [Field R] [NeZero (2 : R)]
    (x y z : SplitWord 1 → R) (target : R)
    (hA : x (cwSplitPair 0 2) + y (cwSplitPair 0 0) + z (cwSplitPair 0 2) = target)
    (hB : x (cwSplitPair 1 1) + y (cwSplitPair 0 0) + z (cwSplitPair 1 1) = target)
    (hC : x (cwSplitPair 0 0) + y (cwSplitPair 0 2) + z (cwSplitPair 0 2) = target)
    (hD : x (cwSplitPair 0 0) + y (cwSplitPair 1 1) + z (cwSplitPair 1 1) = target)
    (hE : x (cwSplitPair 0 2) + y (cwSplitPair 0 2) + z (cwSplitPair 0 0) = target)
    (hF : x (cwSplitPair 1 1) + y (cwSplitPair 1 1) + z (cwSplitPair 0 0) = target) :
    x (cwSplitPair 0 2) = x (cwSplitPair 1 1) := by
  have htwo : (2 : R) * x (cwSplitPair 0 2) = 2 * x (cwSplitPair 1 1) := by
    linear_combination hA - hB - hC + hD + hE - hF
  exact mul_left_cancel₀ (NeZero.ne (2 : R)) htwo

end AlgebraicComplexity.Examples
