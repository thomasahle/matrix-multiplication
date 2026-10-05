/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.TypeClassEntropyLowerCore
import AxiomAudit.Command

/-! Axiom audit for the lightweight arbitrary-type method-of-types lower bound. -/

/- The terminal theorem uses every preceding lemma in this module, so its transitive axiom audit
covers the whole proof chain while avoiding six redundant environment traversals. -/
#assert_axioms
  AlgebraicComplexity.WordType.two_rpow_profileEntropyBits_le_typeClassEntropyLoss_mul_card_typeClass
