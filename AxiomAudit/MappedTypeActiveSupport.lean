/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.MappedTypeActiveSupport
import AxiomAudit.Command

/-!
# Axiom audit for mapped types on active support

This file checks that both support-restriction laws for finite integral-profile pushforwards depend
only on the project's allowlisted classical principles.
-/

#assert_axioms AlgebraicComplexity.WordType.mappedType_subtype_eq_of_eq_zero_outside
#assert_axioms AlgebraicComplexity.WordType.mappedType_activeSupport
