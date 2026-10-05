/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Definitions of finite Kullback--Leibler divergence

This file contains only the two finite KL definitions.  Entropy identities and nonnegativity live
in `Probability/KullbackLeiblerBasic.lean`; deterministic data processing lives in
`Probability/KullbackLeibler.lean`.

Keeping the definitions below the theorem environment lets elementary concentration bounds state
and unfold KL divergence without importing the much larger log-sum/data-processing proof closure.
The historical import continues to re-export these declarations with exactly the same names.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace ProbabilityVector

universe u

variable {I : Type u} [Fintype I]

/-- Kullback--Leibler divergence in nats.  It is intended for a full-support reference vector. -/
noncomputable def klDiv (p q : ProbabilityVector I) : ℝ :=
  ∑ i, p.weight i * Real.log (p.weight i / q.weight i)

/-- Kullback--Leibler divergence measured in bits. -/
noncomputable def klDivBits (p q : ProbabilityVector I) : ℝ :=
  p.klDiv q / Real.log 2

end ProbabilityVector
end AlgebraicComplexity
