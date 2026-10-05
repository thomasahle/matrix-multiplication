/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Analysis.PairedConditionalWordFamilyCoarsenedEntropy

/-!
# Axiom audit for paired coarsened empirical-word entropy bounds

This focused audit checks the reusable two-cell actual-family auxiliary used in the exact/pooled
compatibility count of Claim 6.18 in Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou,
*More Asymmetry Yields Faster Matrix Multiplication*
(`papers/sources/2404.16349/constituent.tex`, lines 404--432).
-/

set_option autoImplicit false

open AlgebraicComplexity

#assert_axioms
  WordType.card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_pairedCoarsenedBounds
