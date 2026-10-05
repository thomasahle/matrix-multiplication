/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.LegalHybridQ20Row44Primary

set_option autoImplicit false

/-!
# Focused axiom audit for the q20 row-44 primary adapter

This companion audits the literal semantic primary-table conversion and the single-entry proof
that zero-based legal-hybrid schedule row 44 has positive parent mass.  It covers no beta-three
cache, reader-realization statement, tensor restriction, logarithmic estimate, or endpoint.
-/

namespace MatrixMultiplication.LegalHybridQ20Row44Primary

#assert_axioms semanticPrimaryTables
#assert_axioms row44_sparseEntry_mem
#assert_axioms row44_topSplitNumerator_pos
#assert_axioms row44_parentSamples_pos

end MatrixMultiplication.LegalHybridQ20Row44Primary
