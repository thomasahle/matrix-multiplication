/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.OneSliceRestriction
import AlgebraicComplexity.Tensor.Restriction

/-!
# Restriction-relation bridge for explicit one-slice certificates

The map-level core deliberately avoids importing the full restriction calculus.  This optional
module supplies the canonical forgetful theorem for clients that need the proposition-level
`Restricts` relation.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {T : Tensor3 K V} {d : ℕ}

namespace OneSliceRestriction

/-- Forget the exposed maps and retain the ordinary restriction proposition. -/
theorem restricts (C : OneSliceRestriction T d) :
    Restricts T (matrixMultiplication (K := K) 1 d 1) :=
  ⟨C.legMap, C.map_eq⟩

end OneSliceRestriction

end AlgebraicComplexity
