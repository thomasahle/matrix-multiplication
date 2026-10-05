/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Finite
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Shannon entropy: lightweight definitions

This module contains only the nats and bits definitions.  Clients which merely state an entropy
identity need not load the theorem closure in `Entropy.lean`.
-/

open scoped BigOperators

namespace AlgebraicComplexity.ProbabilityVector

universe u

variable {I : Type u} [Fintype I]

/-- Shannon entropy of a finite probability vector, measured in nats. -/
noncomputable def entropy (p : ProbabilityVector I) : ℝ :=
  ∑ i, Real.negMulLog (p.weight i)

/-- Shannon entropy of a finite probability vector, measured in bits. -/
noncomputable def entropyBits (p : ProbabilityVector I) : ℝ :=
  p.entropy / Real.log 2

end AlgebraicComplexity.ProbabilityVector
