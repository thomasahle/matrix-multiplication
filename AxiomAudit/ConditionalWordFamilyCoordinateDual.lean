/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ConditionalWordFamilyCoordinateDual
import AxiomAudit.Command

/-! # Axiom audit for coordinate-dual empirical word-family bounds -/

open AlgebraicComplexity

#assert_axioms ProbabilityVector.entropyBits_le_coordinateDual_of_pushforward_eq
#assert_axioms
  WordType.card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_coordinateDual
