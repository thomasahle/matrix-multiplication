/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Analysis.ConditionalFeaturePenaltyRate

/-!
# Axiom audit for conditional-feature penalty-rate normalization

This audit checks the exact bit/nat conversion formalizing the final type-count quotient in
[alman2025more, Claim 6.18], `papers/sources/2404.16349/constituent.tex:388-439`.
-/

set_option autoImplicit false

open AlgebraicComplexity.WordType

#assert_axioms conditionalFeatureEntropyPenaltyBase_eq_exp_entropyBits_sub
#assert_axioms conditionalFeatureEntropyPenaltyBase_eq_two_rpow_entropyBits_sub
