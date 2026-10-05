/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Analysis.RetainedExponentAggregationStrict

/-!
# Axiom audit for the strict retained-exponent aggregation

The strict analogues of the three `RetainedExponentAggregation` assertions in `AxiomAudit.lean`:
a strict common branch floor, its summation over a nonempty family, and the four-family sum with
one strict summand.  They reach no generated data, so they belong to the ordinary focused audit
target rather than to `AxiomAuditCertificate`.

Each `#assert_axioms` fails elaboration if its declaration depends on any axiom other than
`propext`, `Classical.choice`, and `Quot.sound`.
-/

#assert_axioms AlgebraicComplexity.RetainedExponentAggregation.lt_threeWayMin
#assert_axioms AlgebraicComplexity.RetainedExponentAggregation.familyFloor_lt_familyExponent
#assert_axioms
  AlgebraicComplexity.RetainedExponentAggregation.fourFamilyFloor_lt_fourFamilyExponent_of_familyBounds
#assert_axioms
  AlgebraicComplexity.RetainedExponentAggregation.fourFamilyFloor_lt_fourFamilyExponent_of_levelTwo
