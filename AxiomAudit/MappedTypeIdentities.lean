/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.MappedTypeIdentities

set_option autoImplicit false

/-! # Axiom audit for pushforward identities for integral profiles -/

#assert_axioms AlgebraicComplexity.WordType.mappedType_id
#assert_axioms AlgebraicComplexity.WordType.mappedType_congr
#assert_axioms AlgebraicComplexity.WordType.exists_of_mappedType_ne_zero
