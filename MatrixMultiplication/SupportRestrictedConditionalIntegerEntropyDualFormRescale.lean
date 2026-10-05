/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicIntegralProfileEntropyCore
import MatrixMultiplication.DyadicMassEntropy
import MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualForm

set_option autoImplicit false

/-!
# Dyadic rescaling of support-restricted retained forms

Multiplying every source count by `2 ^ extra` and increasing the common bit width by `extra`
represents the same finite mass profile.  The restricted row partitions depend only on the score
weights, so the complete four-term retained-form evaluation is unchanged.
-/

open scoped BigOperators

namespace MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualFormRescale

open AlgebraicComplexity
open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.DyadicIntegralProfileEntropy
open MatrixMultiplication.DyadicMassEntropy
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualForm

noncomputable section

universe u v

/-- A fixed-coordinate source-fiber numerator scales by the same dyadic factor as every source
state. -/
theorem fixedCoordinateFiberNumerator_rescale
    {Z : Type u} {U : Type v} [DecidableEq Z] [Fintype U]
    (extra : ℕ) (coord : U → Z) (numerator : U → ℕ) (z : Z) :
    fixedCoordinateFiberNumerator coord
        (fun state ↦ numerator state * dyadicDenominator extra) z =
      fixedCoordinateFiberNumerator coord numerator z * dyadicDenominator extra := by
  rw [fixedCoordinateFiberNumerator_eq, fixedCoordinateFiberNumerator_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro state _
  by_cases h : coord state = z <;> simp [h]

/-- The exact support-restricted retained-row form is invariant under a matching dyadic rescale
of every source numerator and the common denominator width. -/
theorem retainedRowForm_eval_rescale
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U]
    (bits extra : ℕ) (coord : U → Z) (numerator weight : U → ℕ) :
    Form.eval (bits + extra)
        (retainedRowForm (bits + extra) coord
          (fun state ↦ numerator state * dyadicDenominator extra) weight) =
      Form.eval bits (retainedRowForm bits coord numerator weight) := by
  classical
  have hEntropy :
      weightedEntropyList (bits + extra)
          (sourceNumerators
            (fun state ↦ numerator state * dyadicDenominator extra)) =
        weightedEntropyList bits (sourceNumerators numerator) := by
    change
      weightedEntropyList (bits + extra)
          (MatrixMultiplication.SimplifiedExponentRootRecurrence.numeratorList
            (fun state ↦ numerator state * dyadicDenominator extra)) =
        weightedEntropyList bits
          (MatrixMultiplication.SimplifiedExponentRootRecurrence.numeratorList numerator)
    rw [weightedEntropyList_numeratorList, weightedEntropyList_numeratorList]
    let data : DyadicMassData U := { numerator := numerator }
    exact weightedEntropy_rescale bits extra data
  rw [retainedRowForm_eval, retainedRowForm_eval, hEntropy]
  simp_rw [mass_rescale]
  simp_rw [fixedCoordinateFiberNumerator_rescale]
  simp_rw [mass_rescale]

end

end MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualFormRescale
