/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PositiveWordAppendConst

/-! # Axiom audit for constant-word concatenation

A constant word is the concatenation of constant words, and its legwise corollary. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Tensor.positiveWordAppend_const
#assert_axioms AlgebraicComplexity.Tensor.ofLegs_positiveWordAppend_const
