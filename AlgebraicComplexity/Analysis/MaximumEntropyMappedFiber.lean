/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Entropy

/-!
# Maximum entropy in a finite mapped-coordinate fiber

This module contains the lightweight semantic predicate shared by type counting, independent
products, and coordinate reindexing.  It deliberately has no multinomial or asymptotic imports:
clients that only transport a maximum-entropy statement should not pay for the full method-of-types
development.
-/

namespace AlgebraicComplexity.WordType

universe u v w

variable {I : Type u} [Fintype I]
variable {C : Type v} [Fintype C]
variable {A : C → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- A probability law maximizes entropy among laws with the same finite family of visible
pushforwards. -/
def IsMaximumEntropyInMappedFiber
    (coordinate : ∀ c, I → A c) (p : ProbabilityVector I) : Prop :=
  ∀ q : ProbabilityVector I,
    (∀ c, q.pushforward (coordinate c) = p.pushforward (coordinate c)) →
      q.entropy ≤ p.entropy

end AlgebraicComplexity.WordType
