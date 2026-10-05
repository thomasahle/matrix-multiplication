/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellSurjective

/-! # Axiom audit for the `(0,2,2)` fibre surjectivity

The degree complement of a level-one block, the forced zero-`X` fine letter and its supportedness,
the witness address of a typed `Z` word with its three leg readings, and the injection of the
`alphatilde`-typical type class into the one-segment localized power's support. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63BlockComplement
#assert_axioms AlgebraicComplexity.Examples.dwz63_blockDegree_complement
#assert_axioms AlgebraicComplexity.Examples.dwz63_blockAddress_zero_complement_mem
#assert_axioms AlgebraicComplexity.Examples.dwz63_squareBlockDegree_complement_of_eq_two
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroXFineLetterAddress
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroXFineLetterAddress_X
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroXFineLetterAddress_Y
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroXFineLetterAddress_Z
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroXFineLetterAddress_mem
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroXFineLetter
#assert_axioms AlgebraicComplexity.Examples.dwz63ZeroXFineWitness
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroXFineWitness_equiv
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroXFineWitness_X
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroXFineWitness_Z
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroXFineWitness_mem
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroXFineWitness_coarsens
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_typeClass_le_zeroXFineCellSupport
