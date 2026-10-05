/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.LegalHybridQ20PrimaryTables

set_option autoImplicit false

/-!
# Focused trust audit for the legal-hybrid q20 primary-table source image

This companion audits every declaration in the isolated `PrimaryTables` source image for the q20
top law used in `better_bound/paper.tex:2057-2075`. Generated payload, array-helper, and lower
aggregate declarations have separate focused audit companions. No semantic bridge, logarithmic
estimate, restriction, or endpoint is claimed here.
-/

#assert_axioms MatrixMultiplication.LegalHybridQ20PrimaryTables.PrimaryTables
#assert_axioms MatrixMultiplication.LegalHybridQ20PrimaryTables.primaryTables
#assert_axioms MatrixMultiplication.LegalHybridQ20PrimaryTables.lowerFields_eq_existing
#assert_axioms MatrixMultiplication.LegalHybridQ20PrimaryTables.topSupportAtomIndices
#assert_axioms
  MatrixMultiplication.LegalHybridQ20PrimaryTables.topSupportAtomIndices_strictlyIncreasing
#assert_axioms MatrixMultiplication.LegalHybridQ20PrimaryTables.topSupportAtomIndices_length
#assert_axioms MatrixMultiplication.LegalHybridQ20PrimaryTables.topValueCount_eq
#assert_axioms MatrixMultiplication.LegalHybridQ20PrimaryTables.topNumeratorTotal_eq
