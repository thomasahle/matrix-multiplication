/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.PushedConditionalTypeCounting
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightTypeCore

/-!
# Exact type counting for the CW total-weight quotient

This file specializes the generic pushed-profile method of types to the feature
`cwSplitWordTotalDigit`.  The quotient profile below is exactly the integer pushforward which a
certificate evaluator must use in its compatibility numerators.  The finite upper count therefore
has exponent

`H(cell, totalWeight) - H(cell)`.

The companion lift theorem is equally important: every quotient word counted by that profile has
a fine complete-split lift of the *entire prescribed raw joint type*.  This is what permits a
whole-coarsened constituent to be isolated on the quotient alphabet and subsequently restricted
to the original fine typed constituent without paying for or selecting a quotient fiber.
-/

open scoped BigOperators

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity.WordType

universe u

variable {Cell : Type u} [Fintype Cell]

/-- Exact finite Claim-6.18-style count on the total-weight quotient alphabet.  The only
prefactor is the structural-zero loss already known to be subexponential. -/
theorem cwTotalWeight_card_conditionalTypeClass_le_entropyBase_pow
    (depth : ℕ) (rawProfile : Cell × SplitWord depth → ℕ)
    (cellProfile : Cell → ℕ)
    (hmargin : mappedType Prod.fst rawProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile)
    (k : ℕ) (hk : 0 < k)
    (source : Fin (profileMass cellProfile * k) → Cell)
    (hsource : multiplicity source = proportionalCounts cellProfile k) :
    ((conditionalTypeClass source
        (proportionalCounts
          (cwTotalWeightConditionalProfile depth rawProfile) k)).card : ℝ) ≤
      structuralZeroMultinomialLoss cellProfile k *
        conditionalProfileEntropyBase cellProfile
          (cwTotalWeightConditionalProfile depth rawProfile) ^ k := by
  exact card_pushedConditionalTypeClass_le_entropyBase_pow
    (cwSplitWordTotalDigit depth) rawProfile cellProfile hmargin hmass
      k hk source hsource

end AlgebraicComplexity.Examples
