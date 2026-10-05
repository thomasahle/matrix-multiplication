/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetRelabeling

/-!
# Focused trust audit for recursive target relabelings

These assertions cover the doubled-occurrence stabilizer, its decoded action and exact-target
uniformity, the explicit nested-power lift premise, and the final simultaneous structure-
relabeling package consumed by sparse repair.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

#assert_axioms cwRecursiveReferenceCellPermSubgroup
#assert_axioms cwRecursiveChildOccurrencePartEquiv
#assert_axioms cwRecursiveLabelledChildrenEquiv_childOccurrencePartEquiv_apply
#assert_axioms cwRecursiveChildOccurrencePartEquiv_one
#assert_axioms cwRecursiveChildOccurrencePartEquiv_mul
#assert_axioms cwRecursiveExactTargetFiberParts_childOccurrenceRelabel_iff
#assert_axioms cwRecursiveExactTargetPartChildOccurrenceEquiv
#assert_axioms cwRecursiveExactTargetPartChildOccurrenceEquiv_apply_val
#assert_axioms cwRecursiveExactTargetPartMulAction
#assert_axioms cwRecursiveExactTargetPart_isPretransitive
#assert_axioms cwRecursiveExactTargetUniformOnParts
#assert_axioms CWRecursiveChildOccurrenceRelabelingLift
#assert_axioms cwRecursiveExactTargetUniformStructureRelabelings
