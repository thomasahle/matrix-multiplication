/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedLossHash

set_option autoImplicit false

/-! Focused trust audit for the two typical-word counts of [DuanWuZhou2022] section 6.3 in target
coordinates: `N_X` (the leg-label digit count) and `N_triple` (the joint count), together with the
structure they rest on --- the digit coordinate system of a six-orientation block label, the
two-sided characterization of the six-orientation support, and the leg marginals --- together with
the sharp leg-fiber bound `hsharp` rests on and the loss-free hashing-branch rate.

Everything is unconditional: no hypothesis, no `sorry`, no new axiom. -/

#assert_axioms AlgebraicComplexity.WordType.mappedType_id
#assert_axioms AlgebraicComplexity.WordType.mappedType_congr
#assert_axioms AlgebraicComplexity.WordType.exists_of_mappedType_ne_zero

#assert_axioms AlgebraicComplexity.Examples.dwz63TargetLetter_apply
#assert_axioms AlgebraicComplexity.Examples.dwz63TargetTupleEquiv
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63SymSixPartition_support_iff
#assert_axioms AlgebraicComplexity.Examples.mem_dwz63SymSixPartition_support_iff_target
#assert_axioms AlgebraicComplexity.Examples.dwz63TargetLetter_mem_cwSquareSupport

#assert_axioms AlgebraicComplexity.Examples.mappedType_legRead_dwz63AlphaAddress
#assert_axioms AlgebraicComplexity.Examples.mem_cwSquareSupport_of_dwz63AlphaAddress_ne_zero

#assert_axioms AlgebraicComplexity.Examples.card_dwz63LegTypedWords
#assert_axioms AlgebraicComplexity.Examples.dwz63XTypicalCount_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63XTypicalCount_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_cutoff_pow_le_dwz63XTypicalCount
#assert_axioms AlgebraicComplexity.Examples.dwz63_xRate_pow_le_dwz63XTypicalCount

#assert_axioms AlgebraicComplexity.Examples.card_dwz63TargetTypedWords
#assert_axioms AlgebraicComplexity.Examples.dwz63TargetTypicalWords_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63JointTypicalCount_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63JointTypicalCount_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_cutoff_pow_le_dwz63JointTypicalCount
#assert_axioms AlgebraicComplexity.Examples.dwz63JointTypicalCount_le

#assert_axioms AlgebraicComplexity.Examples.multiplicity_dwz63SymSixDigit_dwz63LegWord
#assert_axioms AlgebraicComplexity.Examples.dwz63LegWord_X_mem_dwz63LegTypedWords
#assert_axioms AlgebraicComplexity.Examples.dwz63LegWord_Z_mem_dwz63LegTypedWords

-- The sharp leg-fiber degree.
#assert_axioms AlgebraicComplexity.Examples.card_legFiber_le_sharpDegree
#assert_axioms AlgebraicComplexity.Examples.card_dwz63JointTypedWords
#assert_axioms AlgebraicComplexity.Examples.dwz63JointTypedWords_subset_targetTypicalWords
#assert_axioms AlgebraicComplexity.Examples.card_legFiber_le_dwz63SharpDegree

-- The hashing-branch rate.
#assert_axioms AlgebraicComplexity.Examples.dwz63_hashingBranch_lt_exp
#assert_axioms AlgebraicComplexity.Examples.dwz63_hashingBranch_pow_le_dwz63XTypicalCount
#assert_axioms AlgebraicComplexity.Examples.dwz63_hrate_of_retentionLoss_le

-- The marginal-typical ambient fiber: the arithmetic bridge only.  The two `Prop`s
-- `Dwz63MarginalAmbientFiberCount` and `Dwz63MarginalAmbientFiberBound` are stated, not claimed,
-- so nothing about them is audited beyond this implication between them.
#assert_axioms AlgebraicComplexity.Examples.dwz63MarginalAmbientFiberBound_of_count

-- The fiber over the marginal-typical ambient, now a theorem, and the `hsharp` it certifies.
#assert_axioms AlgebraicComplexity.Examples.card_dwz63LegFiberWords_mul
#assert_axioms AlgebraicComplexity.Examples.dwz63LegTypicalCount_pos
#assert_axioms AlgebraicComplexity.Examples.card_legFiber_dwz63TargetTypicalWords_mul
#assert_axioms AlgebraicComplexity.Examples.card_legFiber_le_dwz63LegSharpDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63MarginalAmbientFiberBound_XY

-- The marked-count rate `hrate`.
#assert_axioms AlgebraicComplexity.Examples.dwz63XTypicalCount_le_dwz63JointTypicalCount
#assert_axioms AlgebraicComplexity.Examples.dwz63XTypicalCount_mul_sharpDegree_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_xCount_mul_retentionLoss_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_hrate_at_dwz63TargetTypicalWords

-- Subexponentiality of the marked-count loss.
#assert_axioms AlgebraicComplexity.Examples.subexponential_dwz63SharpBehrendLoss
#assert_axioms AlgebraicComplexity.Examples.subexponential_dwz63MarkedLossHash
