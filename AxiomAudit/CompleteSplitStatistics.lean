/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CompleteSplitStatistics
import AxiomAudit.Command

/-! Axiom audit for additive word and exact complete-split statistics. -/

open AlgebraicComplexity

#assert_axioms WordType.sum_word_eq_sum_multiplicity_mul
#assert_axioms WordType.sum_word_eq_of_multiplicity_eq
#assert_axioms CompleteSplitProfile.sum_statistic_of_isConsistent
#assert_axioms CompleteSplitProfile.sum_statistic_eq_of_isConsistent
#assert_axioms CompleteSplitProfile.sum_middleCount_of_isConsistent
