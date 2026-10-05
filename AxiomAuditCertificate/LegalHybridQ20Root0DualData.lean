/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.Generated.LegalHybridQ20Root0DualData

set_option autoImplicit false

/-!
# Audit of the canonical q20 root-zero integer partition

The source is the concrete arithmetic instance of `eq:partition` and `prop:dual`,
`better_bound/paper.tex:2274-2307`, on the root alphabet of CW [coppersmith1990matrix].
Every public declaration is asserted below. The examples additionally instantiate positivity
at the actual integer factors and apply the existing partition-form evaluation theorem.

The form example deliberately uses the simple numerator-one row, not the q20 root law. It
checks the actual coordinate/factor call site and denominator twenty without assuming any
unsatisfied hypotheses. It does not establish root marginal matching or an entropy endpoint.

## Reference

- [coppersmith1990matrix] Don Coppersmith and Shmuel Winograd, *Matrix multiplication via
  arithmetic progressions*.
- Total-Weight manuscript, `better_bound/paper.tex:2274-2307`, `eq:partition` and `prop:dual`.
-/

open MatrixMultiplication.Generated.LegalHybridQ20Root0DualData

#assert_axioms xFactor
#assert_axioms yFactor
#assert_axioms zFactor
#assert_axioms xFactor_pos
#assert_axioms yFactor_pos
#assert_axioms zFactor_pos
#assert_axioms fixedXSubtotal
#assert_axioms fixedXSubtotal_0
#assert_axioms fixedXSubtotal_1
#assert_axioms fixedXSubtotal_2
#assert_axioms fixedXSubtotal_3
#assert_axioms fixedXSubtotal_4
#assert_axioms fixedXSubtotal_5
#assert_axioms fixedXSubtotal_6
#assert_axioms fixedXSubtotal_7
#assert_axioms fixedXSubtotal_8
#assert_axioms fixedXSubtotal_9
#assert_axioms fixedXSubtotal_10
#assert_axioms fixedXSubtotal_11
#assert_axioms fixedXSubtotal_12
#assert_axioms fixedXSubtotal_13
#assert_axioms fixedXSubtotal_14
#assert_axioms fixedXSubtotal_15
#assert_axioms fixedXSubtotal_16
#assert_axioms partitionNumerator
#assert_axioms partitionNumerator_eq_sum_fixedXSubtotal
#assert_axioms partitionNumerator_eq

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.HomogeneousIntegerEntropyDualForm

/-- The literal q20 factors satisfy the three coordinatewise positivity hypotheses. -/
example : (∀ i, 0 < xFactor i) ∧ (∀ i, 0 < yFactor i) ∧ (∀ i, 0 < zFactor i) :=
  ⟨xFactor_pos, yFactor_pos, zFactor_pos⟩

/-- Applying the checked partition at its explicit-state consumer gives the exact q20 integer. -/
example :
    integerPartitionNumeratorOn (shapes 16) Shape.x Shape.y Shape.z xFactor yFactor zFactor =
      83307604927592561572213746647943930712389 :=
  partitionNumerator_eq

/-- A concrete numerator-one row consumes the exact partition through the existing form API. -/
example :
    MatrixMultiplication.SignedDyadicLogForm.Form.eval 20
        (homogeneousPartitionFormOn (shapes 16) (fun _ ↦ 1)
          Shape.x Shape.y Shape.z xFactor yFactor zFactor) =
      MatrixMultiplication.DyadicEntropy.mass 20
          (totalNumeratorOn (shapes 16) (fun _ ↦ 1)) *
        (Real.log (83307604927592561572213746647943930712389 : ℝ) / Real.log 2) := by
  have h := homogeneousPartitionFormOn_eval 20 (shapes 16) (fun _ ↦ 1)
    Shape.x Shape.y Shape.z xFactor yFactor zFactor
  change _ = _ * (Real.log (partitionNumerator : ℝ) / Real.log 2) at h
  rw [partitionNumerator_eq] at h
  exact h
