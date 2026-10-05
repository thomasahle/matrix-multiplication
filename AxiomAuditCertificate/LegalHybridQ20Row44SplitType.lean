/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/
import MatrixMultiplication.LegalHybridQ20Row44SplitType
import AxiomAudit.Command

/-! # Axiom audit of the concrete q20 row44 exact split type

Checks every declaration, including the nonempty instance of [alman2025more]'s ordered law.
-/
set_option autoImplicit false
open MatrixMultiplication.LegalHybridQ20Row44SplitType
#assert_axioms row44SlotEquiv
#assert_axioms row44Numerator
#assert_axioms row44Numerator_ofFn
#assert_axioms row44Numerator_sum
#assert_axioms row44SlotCount
#assert_axioms row44SlotCount_sum
#assert_axioms row44ExactSplitType
#assert_axioms row44ExactSplitType_total
#assert_axioms row44ExactSplitType_nonempty
