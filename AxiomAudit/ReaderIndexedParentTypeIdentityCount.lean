/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ReaderIndexedParentTypeIdentityCount
import AxiomAudit.Command

/-!
# Axiom audit for identity-reader parent-block counting

This focused audit covers the finite cellwise upper bound for the homogeneous-reader case of
`better_bound/paper.tex` at commit `e7317a1d`, Theorem `thm:reader-indexed-parent-type`, lines
3126--3167, following [alman2025more, Claim 6.18] at
`papers/sources/2404.16349/constituent.tex:402-436`.
-/

set_option autoImplicit false

open AlgebraicComplexity.WordType

#assert_axioms
  ReaderIndexedParentModel.card_parentBlocks_le_prod_cellMultinomial_of_identityReaders
