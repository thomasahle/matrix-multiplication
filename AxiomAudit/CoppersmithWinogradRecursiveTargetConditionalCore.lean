/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetConditionalCore

set_option autoImplicit false

/-!
# Axiom audit for recursive CW exact targets as conditional type classes

These checks cover every public declaration in the dependency-light finite bridge from native
recursive parent labels to bounded tagged-cell conditional type classes.  This is the fixed-cell
step used in Claim 6.18 of [alman2025more],
`papers/sources/2404.16349/constituent.tex:376-440`, and in the Total-Weight segmented target
interface at `better_bound/paper.tex:1658-1694,1720-1744,1771-1802`.

No occurrence-support theorem, product-of-multinomials count, tensor restriction, asymptotic rate,
or numerical endpoint is asserted here.

The audited module also has two `private` helpers, `cwRecursiveOrientedCoarseCellToIndex_injective`
and `exists_recursiveFiniteCell_of_total`.  `#assert_axioms` cannot name a private constant, and
it does not need to: each is used only by the public theorems asserted below, so its axiom cone
is contained in theirs and is checked transitively.
-/

#assert_axioms AlgebraicComplexity.Examples.cwRecursiveLabelledChildren_surjective
#assert_axioms AlgebraicComplexity.Examples.cwRecursiveLabelledChildrenEquiv
#assert_axioms AlgebraicComplexity.Examples.cwRecursiveLabelledChildrenEquiv_apply
#assert_axioms
  AlgebraicComplexity.Examples.val_cwRecursiveLabelledChildWord_eq_splitWordWeight
#assert_axioms AlgebraicComplexity.Examples.cwRecursiveOrientedFiniteCellSequence
#assert_axioms
  AlgebraicComplexity.Examples.cwOrientedCoarseCellToIndex_comp_recursiveFiniteCellSequence
#assert_axioms AlgebraicComplexity.Examples.CWRecursiveTargetCoarseTotalSupported
#assert_axioms
  AlgebraicComplexity.Examples.cwRecursiveFiniteCellSplitMultiplicity_eq_cellMultiplicity
#assert_axioms AlgebraicComplexity.Examples.compatibilityTargets_exactProfile_weight_eq
#assert_axioms
  AlgebraicComplexity.Examples.mem_cwRecursiveExactTargetFiberParts_iff_conditionalTypeClass
