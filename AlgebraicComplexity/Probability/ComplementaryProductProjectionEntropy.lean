/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.ComplementaryProductProjectionMarginals
import AlgebraicComplexity.Probability.EntropyChainRule

/-!
# Entropy of a complementary conditional-product reference

The purely algebraic marginal and support theorems live in
`ComplementaryProductProjectionMarginals.lean`.  This module adds the two entropy identities,
keeping semantic occurrence-profile clients independent of the entropy chain-rule closure.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace ComplementaryProductProjectionModel

universe u v w

variable {State : Type u} {Cell : Type v} {Symbol : Type w}
variable [Fintype State] [Fintype Cell] [Fintype Symbol]

/-- Conditional reference entropy is the state-law average of the two child entropies. -/
theorem reference_conditionalEntropy_coarse [DecidableEq State]
    (M : ComplementaryProductProjectionModel State Cell Symbol) :
    M.reference.conditionalEntropy M.coarse =
      ∑ state, M.stateLaw.weight state *
        ((M.childLaw (M.cellOf state)).entropy +
          (M.childLaw (M.cellOf (M.complement state))).entropy) := by
  rw [reference, coarse, ProbabilityVector.conditionalEntropy_joint_fst]
  apply Finset.sum_congr rfl
  intro state _
  rw [ProbabilityVector.entropy_product]

/-- Base-two conditional reference entropy is the state-law average of the two child
entropies. -/
theorem reference_conditionalEntropyBits_coarse [DecidableEq State]
    (M : ComplementaryProductProjectionModel State Cell Symbol) :
    M.reference.conditionalEntropyBits M.coarse =
      ∑ state, M.stateLaw.weight state *
        ((M.childLaw (M.cellOf state)).entropyBits +
          (M.childLaw (M.cellOf (M.complement state))).entropyBits) := by
  unfold ProbabilityVector.conditionalEntropyBits ProbabilityVector.entropyBits
  rw [reference_conditionalEntropy_coarse, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro state _
  ring

end ComplementaryProductProjectionModel
end AlgebraicComplexity
