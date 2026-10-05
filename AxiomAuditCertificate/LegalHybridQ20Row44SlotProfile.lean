/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/
import MatrixMultiplication.LegalHybridQ20Row44SlotProfile
import AxiomAudit.Command

/-! # Axiom audit of the q20 row44 slot profile

Checks every declaration of the finite slot interpretation of [alman2025more]'s ordered law.
-/
set_option autoImplicit false
open MatrixMultiplication.LegalHybridQ20Row44SlotProfile
#assert_axioms row44_parentShape
#assert_axioms row44Pairs
#assert_axioms row44Pairs_eq
#assert_axioms row44Pairs_length
#assert_axioms row44SlotNumerators
#assert_axioms row44SlotNumerators_length
#assert_axioms row44SlotNumerators_sum
#assert_axioms row44Pairs_atoms
#assert_axioms row44SlotEntries
#assert_axioms row44TopEntries_eq_slotEntries
