/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.LegalHybridQ20Row44TopCorrespondence
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Audit of the row-44 sparse/dense ordered-law correspondence

All declarations implementing the q20 ordered alpha correspondence are asserted here.
The mathematical law is [alman2025more], constituent.tex:41-47; the concrete counts are ours.
-/

open MatrixMultiplication.LegalHybridQ20Row44TopCorrespondence

#assert_axioms row44Atom
#assert_axioms row44Atom_mem
#assert_axioms row44_pairAt_eq
#assert_axioms row44_pairIndex_lt
#assert_axioms row44_pairAtom_eq
#assert_axioms row44_selected_massEntries
#assert_axioms row44Entries_lookup
#assert_axioms row44_topSplitNumerator_eq
#assert_axioms row44_topSplitNumerator_sum
