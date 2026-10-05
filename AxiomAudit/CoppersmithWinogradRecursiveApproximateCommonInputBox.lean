/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateCommonInputBoxTiny

set_option autoImplicit false

/-!
# Axiom audit for the recursive CW common approximate-input box

This companion checks the finite restriction and its concrete nonvacuity witness for Total-Weight
Corollary `cor:recursive-common-input-box`, `better_bound/paper.tex:1085-1124`.  The construction
formalizes the common pre-cleanup input box implicit in the three hole classes of
Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou, *More Asymmetry Yields Faster Matrix
Multiplication* [alman2025more],
`papers/sources/2404.16349/constituent.tex:338-348,473-479`.
-/

open AlgebraicComplexity.Examples

#assert_axioms
  cwRecursiveApproximateInputTargetBox_isomorphic_of_positionRelabel

#assert_axioms
  cwRecursiveApproximateCoarsenedAlphaMarginalTerm_constituent_to_commonInputTargetBox

#assert_axioms
  cwRecursiveApproximateCommonInputBox_nonvacuous
