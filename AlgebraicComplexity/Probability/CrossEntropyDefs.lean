/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Definitions for finite cross entropy and absolute continuity

This lightweight file owns the predicates and functions used by structural-support restriction.
The cross-entropy/KL identities remain in `Probability/CrossEntropy.lean`, whose established import
path re-exports every declaration here.
-/

namespace AlgebraicComplexity
namespace ProbabilityVector

universe u

variable {I : Type u} [Fintype I]

/-- Finite absolute continuity: every zero of the reference law is also a zero of the first law. -/
def IsAbsolutelyContinuous (p q : ProbabilityVector I) : Prop :=
  ∀ i, q.weight i = 0 → p.weight i = 0

/-- Every probability vector is absolutely continuous with respect to a full-support reference. -/
theorem isAbsolutelyContinuous_of_reference_pos
    (p q : ProbabilityVector I) (hq : ∀ i, 0 < q.weight i) :
    p.IsAbsolutelyContinuous q := by
  intro i hzero
  exact False.elim ((hq i).ne' hzero)

/-- Cross entropy in nats.  The intended reference vector has full support. -/
noncomputable def crossEntropy (p q : ProbabilityVector I) : ℝ :=
  -p.expectation fun i ↦ Real.log (q.weight i)

/-- Cross entropy measured in bits. -/
noncomputable def crossEntropyBits (p q : ProbabilityVector I) : ℝ :=
  p.crossEntropy q / Real.log 2

end ProbabilityVector
end AlgebraicComplexity
