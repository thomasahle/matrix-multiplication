/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Cslib.Probability.PMF

/-!
# CSLib adapter: probability mass functions

This file is the adapter boundary between this library and CSLib's `Cslib.Probability.PMF`
module, following the dependency policy of `DESIGN.md`: optional external libraries are consumed
only through explicit adapter modules under `AlgebraicComplexity/Adapters/`, which translate the
external declarations into locally named semantic statements.  Downstream files (currently the
optional hashing bridge `AlgebraicComplexity/Combinatorics/HashingProbability.lean`) import this
adapter and use its local names; they must not import `Cslib.*` directly.  This keeps the external
surface auditable in one place: if CSLib's `PMF` utilities move (they are marked for upstreaming
into Mathlib), are renamed, or are dropped as a dependency, only this file changes.

The single fact currently needed from CSLib is that the uniform distribution on a finite nonempty
type is invariant under pushing forward along an equivalence.  It is re-exposed here as
`AlgebraicComplexity.Adapters.CSLib.uniformOfFintype_map_equiv`, proved directly by the CSLib
lemma of the same base name.  This adapter adds no other theory; it sits below the generic
combinatorics/probability layer and imports nothing from the rest of this library.
-/

namespace AlgebraicComplexity.Adapters.CSLib

universe u v

/-- Pushing the uniform distribution on a finite nonempty type `α` forward along an equivalence
`e : α ≃ γ` yields the uniform distribution on `γ`: `(uniformOfFintype α).map e =
uniformOfFintype γ`.  Adapter re-export of `Cslib.Probability.PMF.uniformOfFintype_map_equiv`;
consume this local name rather than the CSLib declaration. -/
theorem uniformOfFintype_map_equiv {α : Type u} {γ : Type v}
    [Fintype α] [Fintype γ] [Nonempty α] [Nonempty γ] (e : α ≃ γ) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype γ :=
  Cslib.Probability.PMF.uniformOfFintype_map_equiv e

end AlgebraicComplexity.Adapters.CSLib
