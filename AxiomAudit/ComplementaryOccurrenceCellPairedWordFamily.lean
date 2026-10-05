/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Analysis.ComplementaryOccurrenceCellPairedWordFamily

/-!
# Axiom audit for cell-quotiented paired actual-family counts

This audit checks the exact integral actual-family count formalizing [alman2025more, Claim 6.18],
`papers/sources/2404.16349/constituent.tex:388-436`.
-/

set_option autoImplicit false

open AlgebraicComplexity.ComplementaryOccurrenceLaw

#assert_axioms
  card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_cellPairProfiles
