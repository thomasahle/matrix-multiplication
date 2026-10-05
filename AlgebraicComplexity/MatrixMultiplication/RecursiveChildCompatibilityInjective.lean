/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RecursiveChildCompatibilityModel

set_option autoImplicit false

/-!
# Injectivity of labelled recursive-child encodings

Splitting every encoded parent chunk into its labelled left and right children loses no
information.  This is the recursive analogue of the pointwise positive-word injectivity lemma:
the two child words reconstruct the parent through `splitWordSuccEquiv`, and injectivity of the
one-chunk encoder then reconstructs the original positive word.

The result is construction-independent and is the only injectivity premise needed when the
loss-free compatibility counter is applied at an arbitrary recursive depth.
-/

namespace AlgebraicComplexity.MoreAsymmetryCompatibility

open Tensor

universe u v

/-- Every leg of the recursive child compatibility model has an injective chunk observation when
the corresponding parent complete-split encoder is injective. -/
theorem recursiveChildCompatibilityModel_chunks_injective
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (partAt : Fin (n + 1) → Part)
    (hinjective : ∀ c, Function.Injective (encode c)) (c : Leg) :
    Function.Injective ((recursiveChildCompatibilityModel encode partAt).chunks c) := by
  exact positiveWordLabelledChildren_injective (encode c) (hinjective c)

end AlgebraicComplexity.MoreAsymmetryCompatibility
