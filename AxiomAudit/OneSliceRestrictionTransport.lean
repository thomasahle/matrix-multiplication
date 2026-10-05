/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.OneSliceRestrictionTransport
import AxiomAudit.Command

/-!
# Axiom audit for one-slice restriction transports

Checks the two transports of an explicit one-slice certificate — along a legwise map and along a
leg permutation — together with the rotated word iteration they enable.  These are the generic
ingredients that let a zero-`X` or zero-`Y` Coppersmith--Winograd family reuse the committed
zero-`Z` certificates instead of re-proving them in coordinates.
-/

open AlgebraicComplexity

/-! ## Transport along a legwise map -/

#assert_axioms Tensor.permute_one
#assert_axioms OneSliceRestriction.precompose
#assert_axioms OneSliceRestriction.precompose_legMap
#assert_axioms OneSliceRestriction.congrTensor
#assert_axioms OneSliceRestriction.congrTensor_rfl
#assert_axioms OneSliceRestriction.ofPermuteOne

/-! ## The rotated frame -/

#assert_axioms OneSliceRestriction.permuteExternal
#assert_axioms OneSliceRestriction.PermutedPositiveSupportWordData
#assert_axioms OneSliceRestriction.ofPermutedPositiveSupportWordData
#assert_axioms OneSliceRestriction.ofPermutedPositivePowerConstituentData
#assert_axioms OneSliceRestriction.permutedPositiveSupportWord
#assert_axioms OneSliceRestriction.permutedPositiveSupportWord_zero
#assert_axioms OneSliceRestriction.permutedPositiveSupportWord_succ
