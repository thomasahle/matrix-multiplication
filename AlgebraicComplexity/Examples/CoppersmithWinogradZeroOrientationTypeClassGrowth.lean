/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.TypeClassEntropyLowerCore
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationTypeClass

set_option autoImplicit false

/-!
# Entropy growth of oriented zero-coordinate CW interfaces

The exact finite count in every orientation realizes the entropy exponent of the first-live-leg
complete-split profile, up to the same explicit fixed-alphabet polynomial loss.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- The full selected CW interface realizes its oriented live-profile entropy rate. -/
theorem two_rpow_profileEntropyBits_le_typeClassEntropyLoss_mul_card_cwOrientedZeroInterface
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (zero : Leg) (hzero : term.index.count zero = 0)
    (hcomplement : ∀ word,
      (term.positivePowerProfile hmultiplicity (secondLiveLeg zero)).counts word =
        (term.positivePowerProfile hmultiplicity (firstLiveLeg zero)).counts
          (complementSplitWord word)) :
    (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * WordType.profileEntropyBits
        (term.positivePowerProfile hmultiplicity (firstLiveLeg zero)).counts) ≤
      WordType.typeClassEntropyLoss (SplitWord depth) (n + 1) *
        (((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card : ℕ) : ℝ) := by
  have hcount := card_cwSelectedExactInterfaceTerm_zero_eq_card_typeClass
    K q term hmultiplicity zero hzero hcomplement
  change (cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card =
    (WordType.typeClass (n + 1)
      (term.positivePowerProfile hmultiplicity (firstLiveLeg zero)).counts).card at hcount
  have htype := WordType.two_rpow_profileEntropyBits_le_typeClassEntropyLoss_mul_card_typeClass
    (term.positivePowerProfile hmultiplicity (firstLiveLeg zero)).counts
    (term.positivePowerProfile hmultiplicity (firstLiveLeg zero)).isType (Nat.succ_pos n)
  rw [← hcount] at htype
  exact htype

end AlgebraicComplexity.Examples
