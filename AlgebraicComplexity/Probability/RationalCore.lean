/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Finite
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order

/-!
# Core exact rational probability data

This file contains the small representation bridge needed by exact certificate tables: rational
coordinates, their simplex predicate, and their interpretation as a real `ProbabilityVector`.
It deliberately does not import entropy, Kullback--Leibler divergence, or Pinsker inequalities.
Modules needing rational discrepancy bounds should import `Probability.Rational`, which extends
this core without changing its public declarations.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u

/-- Raw rational coordinates for a probability vector. Validity is kept separate so a generated
certificate can check a whole family with one decidable theorem. -/
structure RationalProbabilityData (ι : Type u) where
  weight : ι → ℚ

namespace RationalProbabilityData

variable {ι : Type u} [Fintype ι]

/-- Exact simplex predicate for rational certificate data. -/
def IsProbability (p : RationalProbabilityData ι) : Prop :=
  (∀ i, 0 ≤ p.weight i) ∧ ∑ i, p.weight i = 1

/-- Interpret a valid rational table as a real probability vector. -/
noncomputable def toReal (p : RationalProbabilityData ι) (hp : p.IsProbability) :
    ProbabilityVector ι where
  weight i := (p.weight i : ℝ)
  nonneg i := Rat.cast_nonneg.mpr (hp.1 i)
  total := by
    have htotal := congrArg (fun q : ℚ ↦ (q : ℝ)) hp.2
    simpa only [Rat.cast_sum, Rat.cast_one] using htotal

/-- Interpreting rational data as a real probability vector casts each coordinate to `ℝ`. -/
@[simp] theorem toReal_weight (p : RationalProbabilityData ι) (hp : p.IsProbability) (i : ι) :
    (p.toReal hp).weight i = (p.weight i : ℝ) :=
  rfl

end RationalProbabilityData

end AlgebraicComplexity
