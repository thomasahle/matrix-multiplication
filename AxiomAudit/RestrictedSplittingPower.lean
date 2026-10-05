/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingPower

/-! Focused trust audit for the restricted-splitting tensor power `T^{⊗n}[α̃]` of
`[DuanWuZhou2022]` Definition 2.14, its `claim:degen` splitting degeneration, and the tiny
inhabited regression instance that rules out a vacuous support predicate. -/

#assert_axioms AlgebraicComplexity.Tensor.PartitionedTensor.mem_restrictedSplittingPower_support
#assert_axioms AlgebraicComplexity.Tensor.Restricts.partitionedPositivePower_restrictedSplittingPower
#assert_axioms AlgebraicComplexity.Tensor.Restricts.power_restrictedSplittingPower
#assert_axioms AlgebraicComplexity.SplitRestriction.keeps_append
#assert_axioms AlgebraicComplexity.Tensor.Restricts.restrictedSplittingPower_binaryDivision
#assert_axioms AlgebraicComplexity.Tensor.Restricts.restrictedSplittingPower_ternaryDivision
#assert_axioms AlgebraicComplexity.Tensor.Restricts.zRestrictedSplittingPower_binaryDivision
#assert_axioms AlgebraicComplexity.tinyMixedAddress_mem_restrictedSplittingPower
#assert_axioms AlgebraicComplexity.tinyConstantAddress_not_mem_restrictedSplittingPower
#assert_axioms AlgebraicComplexity.tiny_restrictedSplittingPower_binaryDivision
