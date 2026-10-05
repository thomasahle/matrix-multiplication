/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.Generated.LegalHybridQ20Row44Top

set_option autoImplicit false

/-!
# Axiom audit for the exact q20 row-44 sparse selection

Every declaration of the selected sparse entries and their exact numerator total is checked here.
The candidate is described in `better_bound/paper.tex:148-159` (draft status).
This companion claims no tensor interpretation or exponent endpoint.
The surrounding recursive framework is described in [duan2023faster] and [alman2025more].
-/

namespace MatrixMultiplication.Generated.LegalHybridQ20Row44Top

#assert_axioms entriesAtAddresses
#assert_axioms entriesAtAddresses_append
#assert_axioms entriesAtAddresses_eq_nil_of_disjoint
#assert_axioms entriesAtAddresses_append_image
#assert_axioms row44Atoms
#assert_axioms row44Atoms_bounds
#assert_axioms row44Entries
#assert_axioms row44_block1_eq
#assert_axioms row44_block2_eq
#assert_axioms row44_block3_eq
#assert_axioms row44_top0_eq
#assert_axioms row44_top1_eq
#assert_axioms row44TopEntries
#assert_axioms row44TopEntries_eq
#assert_axioms row44TopEntries_total

end MatrixMultiplication.Generated.LegalHybridQ20Row44Top
