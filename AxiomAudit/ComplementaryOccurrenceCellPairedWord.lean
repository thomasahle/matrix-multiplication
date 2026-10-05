/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceCellPairedWord

/-!
# Trust audit for the cell-quotiented paired-word bridge

This audits the arbitrary-cell integral profile step of [alman2025more, Claim 6.18],
`papers/sources/2404.16349/constituent.tex:388-436`.
-/

#assert_axioms
  AlgebraicComplexity.ComplementaryOccurrenceLaw.isPooledMarginalProfile_of_cellPairWords
