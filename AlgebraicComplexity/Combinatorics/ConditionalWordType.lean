/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.Subexponential
import AlgebraicComplexity.Combinatorics.ConditionalWordTypeCore

/-!
# Conditional multiplicity classes of finite words

This compatibility wrapper re-exports the dependency-minimal finite API from
`ConditionalWordTypeCore` and adds its asymptotic type-count estimate.
-/

namespace AlgebraicComplexity.WordType

universe u

/-- For every fixed finite alphabet, the number of empirical word types is a subexponential
loss.  Combined with `card_types_le`, this is the reusable asymptotic form of the polynomial
type-count bound. -/
theorem card_types_subexponential (I : Type u) [Fintype I] :
    Growth.Subexponential (fun n ↦ ((types I n).card : ℝ)) := by
  apply Growth.Subexponential.mono
    (Growth.Subexponential.natCast_succ_pow (Fintype.card I))
  · intro n
    positivity
  · intro n
    exact_mod_cast card_types_le I n

end AlgebraicComplexity.WordType
