/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.TypeClassEntropyLowerCore
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroTypeClass

/-!
# Entropy growth of zero-coordinate CW interfaces

This is the sequence-ready quantitative consequence of the exact CW type-class bijection.  It
uses the same named polynomial loss as the general method of types and therefore introduces no
new asymptotic hypothesis.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- The entire selected zero-`Z` CW interface realizes the entropy rate of its exact `X`
complete-split profile, up to the explicit polynomial method-of-types loss. -/
theorem two_rpow_profileEntropyBits_le_typeClassEntropyLoss_mul_card_cwZeroInterface
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (hcomplement : ∀ word,
      (term.positivePowerProfile hmultiplicity .Y).counts word =
        (term.positivePowerProfile hmultiplicity .X).counts
          (complementSplitWord word)) :
    (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) *
        WordType.profileEntropyBits
          (term.positivePowerProfile hmultiplicity .X).counts) ≤
      WordType.typeClassEntropyLoss (SplitWord depth) (n + 1) *
        (((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card : ℕ) : ℝ) := by
  have hcount := card_cwSelectedExactInterfaceTerm_zeroZ_eq_card_typeClass
    K q term hmultiplicity hz hcomplement
  change (cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card =
    (WordType.typeClass (n + 1)
      (term.positivePowerProfile hmultiplicity .X).counts).card at hcount
  have htype := WordType.two_rpow_profileEntropyBits_le_typeClassEntropyLoss_mul_card_typeClass
    (term.positivePowerProfile hmultiplicity .X).counts
    (term.positivePowerProfile hmultiplicity .X).isType (Nat.succ_pos n)
  rw [← hcount] at htype
  exact htype

end AlgebraicComplexity.Examples
