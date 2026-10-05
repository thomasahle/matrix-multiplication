/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationOneSlice
import AxiomAudit.Command

/-!
# Axiom audit for rotated zero-coordinate one-slice chunks

Checks the leg-indexed dimension bookkeeping on a zero fibre, the leg-indexed word statistics, and
the rotated word and chunk certificates, including the three named orientations.  The zero-`Z`
instance is checked as well: it is what certifies that the leg-indexed construction subsumes the
committed one.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

/-! ## Dimensions on a zero fibre -/

#assert_axioms cwBaseConstituentDimension_zeroLeg_eq_one_of_eq_zero
#assert_axioms cwBaseConstituentDimension_firstLiveLeg_eq_one_of_eq_zero
#assert_axioms cwBaseConstituentDimension_secondLiveLeg_eq_pow_middleIndicator_of_eq_zero

/-! ## Word statistics -/

#assert_axioms cwSupportedWordMiddleCount
#assert_axioms cwSupportedWordMiddleCount_X
#assert_axioms positiveSupportWord_letter_eq_zero_of_address_eq_const
#assert_axioms positiveWordProduct_cwBaseDimension_secondLiveLeg_eq_pow_middleCount_of_eq_const
#assert_axioms splitWordMiddleCount_cwChunkSplitWord_positiveSupportWordBlockAddress_leg

/-! ## The rotated word and chunk certificates -/

#assert_axioms cwZeroBaseRotatedWordData
#assert_axioms cwZeroBaseRotatedWordOneSliceRestriction
#assert_axioms cwZeroChunkRotatedOneSliceRestriction
#assert_axioms cwZeroXChunkRotatedOneSliceRestriction
#assert_axioms cwZeroYChunkRotatedOneSliceRestriction
#assert_axioms cwZeroZChunkRotatedOneSliceRestriction
