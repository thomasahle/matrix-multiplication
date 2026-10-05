/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Analysis.PooledMarginalProjectionWordFamily

/-!
# Axiom audit for sparse pooled-projection actual-family counting

This checks the generic candidate-first method-of-types bridge used to formalize the fixed-fine
maximum-entropy step of [alman2025more, Claim 6.18],
`papers/sources/2404.16349/constituent.tex:388-436`.
-/

set_option autoImplicit false

#assert_axioms
  AlgebraicComplexity.WordType.card_words_le_conditionalFeatureEntropyLoss_mul_profileConditionalEntropyBitsBase_pow_of_pooledMarginalProjection
