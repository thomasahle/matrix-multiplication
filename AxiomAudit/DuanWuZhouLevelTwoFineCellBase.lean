/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellBase

/-! # Axiom audit for the fine-letter coherent base

The transparent block-address exponent and dimension of a fine letter, and the zero-`X` and
zero-`Y` coherent bases indexed by fine block addresses.  The two bases go through
`Classical.choice` to decode a supported fine address back to its level-one word; the decode is
confined to the proof, and the dimension they carry is the choice-free
`dwz63FineDimension = q ^ dwz63FineOnes`. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63FineOnes
#assert_axioms AlgebraicComplexity.Examples.dwz63FineDimension
#assert_axioms AlgebraicComplexity.Examples.dwz63FineZeroXBase
#assert_axioms AlgebraicComplexity.Examples.dwz63FineZeroYBase
