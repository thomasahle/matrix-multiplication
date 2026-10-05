/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.Generated.LegalHybridQ20RootDualData

set_option autoImplicit false

/-!
# Audit of the six canonical q20 integer partitions

The source instantiates `eq:partition` and `prop:dual`,
`better_bound/paper.tex:2274-2307`, on the root alphabet of CW [coppersmith1990matrix].
Every declaration is asserted below, and actual consumer examples use all six literal roots.

The form example uses a concrete numerator-one row, not the q20 root law. It checks the
coordinate/factor call site and denominator twenty without claiming marginal matching,
the complete dual inequality or an exponent endpoint.

## Reference

- [coppersmith1990matrix] Don Coppersmith and Shmuel Winograd, *Matrix multiplication via
  arithmetic progressions*.
- Total-Weight manuscript, `better_bound/paper.tex:2274-2307`, `eq:partition` and `prop:dual`.
-/

open MatrixMultiplication.Generated.LegalHybridQ20RootDualData

#assert_axioms root1XFactor
#assert_axioms root1XFactor_pos
#assert_axioms root1YFactor
#assert_axioms root1YFactor_pos
#assert_axioms root1ZFactor
#assert_axioms root1ZFactor_pos
#assert_axioms root4XFactor
#assert_axioms root4XFactor_pos
#assert_axioms root4YFactor
#assert_axioms root4YFactor_pos
#assert_axioms root4ZFactor
#assert_axioms root4ZFactor_pos
#assert_axioms root5XFactor
#assert_axioms root5XFactor_pos
#assert_axioms root5YFactor
#assert_axioms root5YFactor_pos
#assert_axioms root5ZFactor
#assert_axioms root5ZFactor_pos
#assert_axioms xFactor
#assert_axioms xFactor_pos
#assert_axioms yFactor
#assert_axioms yFactor_pos
#assert_axioms zFactor
#assert_axioms zFactor_pos
#assert_axioms fixedXSubtotal
#assert_axioms fixedXSubtotal_root1_0
#assert_axioms fixedXSubtotal_root1_1
#assert_axioms fixedXSubtotal_root1_2
#assert_axioms fixedXSubtotal_root1_3
#assert_axioms fixedXSubtotal_root1_4
#assert_axioms fixedXSubtotal_root1_5
#assert_axioms fixedXSubtotal_root1_6
#assert_axioms fixedXSubtotal_root1_7
#assert_axioms fixedXSubtotal_root1_8
#assert_axioms fixedXSubtotal_root1_9
#assert_axioms fixedXSubtotal_root1_10
#assert_axioms fixedXSubtotal_root1_11
#assert_axioms fixedXSubtotal_root1_12
#assert_axioms fixedXSubtotal_root1_13
#assert_axioms fixedXSubtotal_root1_14
#assert_axioms fixedXSubtotal_root1_15
#assert_axioms fixedXSubtotal_root1_16
#assert_axioms fixedXSubtotal_root4_0
#assert_axioms fixedXSubtotal_root4_1
#assert_axioms fixedXSubtotal_root4_2
#assert_axioms fixedXSubtotal_root4_3
#assert_axioms fixedXSubtotal_root4_4
#assert_axioms fixedXSubtotal_root4_5
#assert_axioms fixedXSubtotal_root4_6
#assert_axioms fixedXSubtotal_root4_7
#assert_axioms fixedXSubtotal_root4_8
#assert_axioms fixedXSubtotal_root4_9
#assert_axioms fixedXSubtotal_root4_10
#assert_axioms fixedXSubtotal_root4_11
#assert_axioms fixedXSubtotal_root4_12
#assert_axioms fixedXSubtotal_root4_13
#assert_axioms fixedXSubtotal_root4_14
#assert_axioms fixedXSubtotal_root4_15
#assert_axioms fixedXSubtotal_root4_16
#assert_axioms fixedXSubtotal_root5_0
#assert_axioms fixedXSubtotal_root5_1
#assert_axioms fixedXSubtotal_root5_2
#assert_axioms fixedXSubtotal_root5_3
#assert_axioms fixedXSubtotal_root5_4
#assert_axioms fixedXSubtotal_root5_5
#assert_axioms fixedXSubtotal_root5_6
#assert_axioms fixedXSubtotal_root5_7
#assert_axioms fixedXSubtotal_root5_8
#assert_axioms fixedXSubtotal_root5_9
#assert_axioms fixedXSubtotal_root5_10
#assert_axioms fixedXSubtotal_root5_11
#assert_axioms fixedXSubtotal_root5_12
#assert_axioms fixedXSubtotal_root5_13
#assert_axioms fixedXSubtotal_root5_14
#assert_axioms fixedXSubtotal_root5_15
#assert_axioms fixedXSubtotal_root5_16
#assert_axioms partitionNumerator
#assert_axioms expectedPartition
#assert_axioms partitionNumerator_eq_sum_fixedXSubtotal
#assert_axioms constantPartition_eq
#assert_axioms partitionNumerator_eq

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.HomogeneousIntegerEntropyDualForm

/-- The literal factors satisfy the three positivity hypotheses at every actual q20 root. -/
example (root : Fin 6) :
    (∀ i, 0 < xFactor root i) ∧ (∀ i, 0 < yFactor root i) ∧ (∀ i, 0 < zFactor root i) :=
  ⟨xFactor_pos root, yFactor_pos root, zFactor_pos root⟩

/-- The existing explicit-state consumer gets the exact partition at canonical root 0. -/
example :
    integerPartitionNumeratorOn (shapes 16) Shape.x Shape.y Shape.z
        (xFactor 0) (yFactor 0) (zFactor 0) =
      83307604927592561572213746647943930712389 :=
  partitionNumerator_eq 0

/-- The existing explicit-state consumer gets the exact partition at canonical root 1. -/
example :
    integerPartitionNumeratorOn (shapes 16) Shape.x Shape.y Shape.z
        (xFactor 1) (yFactor 1) (zFactor 1) =
      5876302254208851909486182247482668698951 :=
  partitionNumerator_eq 1

/-- The existing explicit-state consumer gets the exact partition at canonical root 2. -/
example :
    integerPartitionNumeratorOn (shapes 16) Shape.x Shape.y Shape.z
        (xFactor 2) (yFactor 2) (zFactor 2) =
      12121908864682443651812224401408 :=
  partitionNumerator_eq 2

/-- The existing explicit-state consumer gets the exact partition at canonical root 3. -/
example :
    integerPartitionNumeratorOn (shapes 16) Shape.x Shape.y Shape.z
        (xFactor 3) (yFactor 3) (zFactor 3) =
      12121908864682443651812224401408 :=
  partitionNumerator_eq 3

/-- The existing explicit-state consumer gets the exact partition at canonical root 4. -/
example :
    integerPartitionNumeratorOn (shapes 16) Shape.x Shape.y Shape.z
        (xFactor 4) (yFactor 4) (zFactor 4) =
      282088041119429551885567349491709846499805 :=
  partitionNumerator_eq 4

/-- The existing explicit-state consumer gets the exact partition at canonical root 5. -/
example :
    integerPartitionNumeratorOn (shapes 16) Shape.x Shape.y Shape.z
        (xFactor 5) (yFactor 5) (zFactor 5) =
      407013735975715118615493469577801822336350 :=
  partitionNumerator_eq 5

/-- A numerator-one row consumes each exact partition through the existing logarithmic form API. -/
example (root : Fin 6) :
    MatrixMultiplication.SignedDyadicLogForm.Form.eval 20
        (homogeneousPartitionFormOn (shapes 16) (fun _ ↦ 1)
          Shape.x Shape.y Shape.z (xFactor root) (yFactor root) (zFactor root)) =
      MatrixMultiplication.DyadicEntropy.mass 20
          (totalNumeratorOn (shapes 16) (fun _ ↦ 1)) *
        (Real.log (expectedPartition root : ℝ) / Real.log 2) := by
  have h := homogeneousPartitionFormOn_eval 20 (shapes 16) (fun _ ↦ 1)
    Shape.x Shape.y Shape.z (xFactor root) (yFactor root) (zFactor root)
  change _ = _ * (Real.log (partitionNumerator root : ℝ) / Real.log 2) at h
  rw [partitionNumerator_eq] at h
  exact h
