/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordTypeCore
import AxiomAudit.Command

/-! Axiom audit for exact finite word types. -/

#assert_axioms AlgebraicComplexity.WordType.multiplicity
#assert_axioms AlgebraicComplexity.WordType.types
#assert_axioms AlgebraicComplexity.WordType.typeClass
#assert_axioms AlgebraicComplexity.WordType.mem_typeClass
#assert_axioms AlgebraicComplexity.WordType.sum_multiplicity
#assert_axioms AlgebraicComplexity.WordType.multiplicity_const_fin_one
#assert_axioms AlgebraicComplexity.WordType.multiplicity_eq_card_fiber
#assert_axioms AlgebraicComplexity.WordType.multiplicity_reindex
#assert_axioms AlgebraicComplexity.WordType.multiplicity_mem_types
#assert_axioms AlgebraicComplexity.WordType.mem_types
