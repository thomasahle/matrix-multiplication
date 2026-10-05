/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.EntropyDefs
import AlgebraicComplexity.Probability.IntegralProfileEntropyDefs
import AlgebraicComplexity.Probability.IntegralProfileProbabilityCore

/-!
# Lightweight integral probability profiles

This module connects the definition-only integral-profile entropy in
`IntegralProfileEntropyDefs` to the concrete finite probability vector in
`IntegralProfileProbabilityCore`.  It proves that both representations have the same entropy.
It has no Stirling, multinomial, growth, or tensor imports.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u

variable {I : Type u} [Fintype I]

/-- Entropy of the normalized empirical distribution is the profile entropy. -/
theorem normalizedProfileProbability_entropy
    (a : I → ℕ) (hmass : 0 < profileMass a) :
    (normalizedProfileProbability a hmass).entropy = profileEntropyNats a := by
  rfl

end AlgebraicComplexity.WordType
