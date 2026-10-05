/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SimplifiedExponentRecursiveConstituent

/-!
# Axiom audit for recursive-constituent projection

This focused audit checks that the logical-`X` branch-form projection theorem uses only the
project's allowlisted classical axioms.
-/

open AxiomAudit

#assert_axioms MatrixMultiplication.SimplifiedExponentRecursiveConstituent.LocalRows.branchForm_zero_congr
