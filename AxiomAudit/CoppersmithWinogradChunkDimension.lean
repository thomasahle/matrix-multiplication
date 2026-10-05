/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradChunkDimension
import AxiomAudit.Command

/-!
# Axiom audit for canonical CW chunk dimensions

Checks the support-word recovery and exact product dimension definitions independently of the
typed-leaf and entropy stack.
-/

open AlgebraicComplexity.Examples

#assert_axioms positiveWordProduct_pos_of_forall
#assert_axioms cwBaseConstituentDimension_pos
#assert_axioms cwChunkSupportedWordOfAddress
#assert_axioms positiveSupportWordBlockAddress_cwChunkSupportedWordOfAddress
#assert_axioms cwChunkConstituentDimension
#assert_axioms cwChunkConstituentDimension_pos
