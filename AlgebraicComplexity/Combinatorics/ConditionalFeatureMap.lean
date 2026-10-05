/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ConditionalWordTypeCore

/-! # Lightweight visible-feature maps for conditional word types -/

namespace AlgebraicComplexity.WordType

universe u v w

variable {S : Type u} {T : Type v} {C : Type w}

/-- Map a full `(source, target)` letter to its visible `(source, feature)` letter. -/
def conditionalFeatureMap (feature : T → C) : S × T → S × C :=
  fun letter ↦ (letter.1, feature letter.2)

@[simp] theorem conditionalFeatureMap_jointWord
    (source : Fin n → S) (feature : T → C) (target : Fin n → T) :
    conditionalFeatureMap feature ∘ jointWord source target =
      jointWord source (feature ∘ target) := by
  rfl

end AlgebraicComplexity.WordType
