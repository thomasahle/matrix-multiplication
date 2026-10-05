/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradExactSelectionCore
import AxiomAudit.Command

/-! Axiom audit for the lightweight exact CW selector. -/

open AlgebraicComplexity.Examples

#assert_axioms cwSelectedExactInterfaceTerm
