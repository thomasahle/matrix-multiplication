/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.PermutedSharedOneSliceFiber
import AxiomAudit.Command

/-!
# Axiom audit for the rotated shared-fibre fusion

Checks the legwise-equivalence transport, the dependent-cast toolkit, the certificate transport
onto the constituents of a leg-permuted partition, and the fusion theorem itself: a fibre shared on
an arbitrary leg fuses to one matrix-multiplication tensor, in the rotated frame.
-/

open AlgebraicComplexity AlgebraicComplexity.CTensor

/-! ## Transport across a legwise retyping -/

#assert_axioms OneSliceRestriction.ofMapEquiv
#assert_axioms OneSliceRestriction.ofMapEquiv_legMap
#assert_axioms OneSliceRestriction.comp_cast_symm_heq
#assert_axioms OneSliceRestriction.comp_left_heq
#assert_axioms OneSliceRestriction.ofPermuteConstituent
#assert_axioms OneSliceRestriction.ofPermuteConstituent_legMap

/-! ## The rotated fusion -/

#assert_axioms PermutedSharedOneSliceFiberData.sourceAddress
#assert_axioms PermutedSharedOneSliceFiberData.toSharedOneSliceFiberData
#assert_axioms PermutedSharedOneSliceFiberData.restricts_permute_oneSliceMatrixMultiplication
