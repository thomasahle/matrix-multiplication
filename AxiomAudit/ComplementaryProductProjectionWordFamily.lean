/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Analysis.ComplementaryProductProjectionWordFamily

/-!
# Axiom audit for complementary-product actual-family counting

This audit checks the pooled ordered-parent counting theorem used by the fixed-fine numerator
step of [alman2025more, Claim 6.18],
`papers/sources/2404.16349/constituent.tex:388-436`.
-/

set_option autoImplicit false

open AlgebraicComplexity
open AlgebraicComplexity.WordType

#assert_axioms
  card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_complementaryProductProjection
