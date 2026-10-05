/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.PushedProfileTypeCountingCore
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightCore

/-!
# Exact finite total-weight quotient profiles

This analysis-free module defines the integer pushforward used by total-weight counting and proves
its exact marginal and fine-lift properties.  Entropy bounds are kept in the sibling
`CoppersmithWinogradTotalWeightTypeCounting` module.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity.WordType

universe u

variable {Cell : Type u} [Fintype Cell]

/-- Push the complete-split coordinate of a joint cell/split profile to its total-weight digit. -/
noncomputable def cwTotalWeightConditionalProfile (depth : ℕ)
    (rawProfile : Cell × SplitWord depth → ℕ) :
    Cell × CWCoarseDigit depth → ℕ :=
  mappedType
    (conditionalFeatureMap (cwSplitWordTotalDigit depth)) rawProfile

/-- Total-weight pushforward preserves the prescribed cell marginal exactly. -/
theorem cwTotalWeightConditionalProfile_fst
    (depth : ℕ) (rawProfile : Cell × SplitWord depth → ℕ) :
    mappedType Prod.fst (cwTotalWeightConditionalProfile depth rawProfile) =
      mappedType Prod.fst rawProfile := by
  exact mappedType_fst_pushedConditionalProfile
    (cwSplitWordTotalDigit depth) rawProfile

/-- Every total-weight target word of the pushed joint type has a fine complete-split lift with
the full prescribed raw joint type. -/
theorem cwTotalWeight_exists_fineConditionalTarget
    (depth : ℕ) (rawProfile : Cell × SplitWord depth → ℕ)
    (source : Fin n → Cell)
    (hraw : rawProfile ∈ types (Cell × SplitWord depth) n)
    (coarseTarget : Fin n → CWCoarseDigit depth)
    (hcoarseTarget : coarseTarget ∈ conditionalTypeClass source
      (cwTotalWeightConditionalProfile depth rawProfile)) :
    ∃ fineTarget : Fin n → SplitWord depth,
      fineTarget ∈ conditionalTypeClass source rawProfile ∧
        cwSplitWordTotalDigit depth ∘ fineTarget = coarseTarget := by
  exact exists_fineConditionalTarget_of_mem_pushedConditionalTypeClass
    (cwSplitWordTotalDigit depth) rawProfile source hraw
      coarseTarget hcoarseTarget

end AlgebraicComplexity.Examples
