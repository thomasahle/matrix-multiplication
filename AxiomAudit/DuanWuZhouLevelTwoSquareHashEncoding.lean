/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSquareHashEncoding

set_option autoImplicit false

/-! # Axiom audit for the plain fifteen-letter square hashing encoding

The radix-five alphabet and constant target of the plain natural-number encoding, the field-valued
encoding it casts to at characteristic floor five, its hashing target, and the definitional
alphabet bridge between the partition's own support and the bare fifteen-address alphabet. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63SquareNatEncoding_alphabet
#assert_axioms AlgebraicComplexity.Examples.dwz63SquareNatEncoding_natTarget
#assert_axioms AlgebraicComplexity.Examples.dwz63SquareHashEncoding
#assert_axioms AlgebraicComplexity.Examples.dwz63SquareHashEncoding_target
#assert_axioms AlgebraicComplexity.Examples.cwSquarePartitionedTensor_support_dwz63Q
#assert_axioms AlgebraicComplexity.Examples.dwz63SquareHashEncodingBare
#assert_axioms AlgebraicComplexity.Examples.dwz63SquareHashEncodingBare_eq
