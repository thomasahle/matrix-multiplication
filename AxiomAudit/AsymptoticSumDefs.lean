/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.AsymptoticSumDefs

/-!
# Axiom audit for the numerical asymptotic-sum leaf

This focused audit keeps the constant-family normalization checked independently of the full
Schönhage theorem closure.
-/

#assert_axioms AlgebraicComplexity.asymptoticSum_const
