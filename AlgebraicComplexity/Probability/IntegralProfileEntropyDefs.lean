/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.IntegralProfileCounts
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Entropy definitions for integral profiles

This definition-only leaf assigns Shannon entropy to a finite integral profile after normalization
by its total mass.  It contains no probability-vector representation, multinomial estimate,
Stirling bound, or asymptotic theorem.

`IntegralProfileCore` and `TypeClassEntropyLowerCore` import and re-export this module, so moving
the definitions here does not change their public names or meanings.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u

variable {I : Type u} [Fintype I]

/-- Shannon entropy in nats of the normalized integral profile. -/
noncomputable def profileEntropyNats (a : I → ℕ) : ℝ :=
  ∑ i, Real.negMulLog ((a i : ℝ) / (profileMass a : ℝ))

/-- Shannon entropy of the normalized integral profile, in bits. -/
noncomputable def profileEntropyBits (a : I → ℕ) : ℝ :=
  profileEntropyNats a / Real.log 2

end AlgebraicComplexity.WordType
