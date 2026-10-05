/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.FiniteTypicalProfileUniformization
import AxiomAudit.Command

/-!
# Axiom audit for finite typical-profile uniformization

These declarations formalize the finite maximum and uniform loss-envelope steps used in
[alman2025more, Claim 6.18],
`papers/sources/2404.16349/constituent.tex:362-385,438-440`.  They assert no construction-specific
typical alphabet, compatibility relation, denominator normalization, tensor restriction, or
matrix-multiplication endpoint.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.WordType.conditionalFeatureEntropyLossOneEnvelope
#assert_axioms AlgebraicComplexity.WordType.conditionalFeatureEntropyLoss_one_le_envelope
#assert_axioms AlgebraicComplexity.WordType.conditionalFeatureEntropyLossOneEnvelope_subexponential
#assert_axioms AlgebraicComplexity.WordType.cast_finset_sup_count_le_typicalProfileUniformBound
