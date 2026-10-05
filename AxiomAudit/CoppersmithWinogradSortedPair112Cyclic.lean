/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPair112Cyclic

set_option autoImplicit false

/-!
# Axiom audit for cyclic extraction from the sorted-pair CW `(112)` residual

This companion enforces the trust boundary for the exact finite composition from a complete
sorted-pair residual power, through cyclic symmetrization and shared-Z C-tensor grouping, to the
corresponding nested family of square matrix-multiplication tensors.

The audited theorem formalizes the structural part of [CoppersmithWinograd1990, pp. 270--272], as
mapped in `papers/notes/MMult1987.tex:226-259`.  The distinct modern 64-address route is summarized
at `papers/notes/MMult1987.tex:261-285`; it is not asserted here.  This theorem asserts no entropy,
optimization, or exponent bound.
-/

#assert_axioms
  AlgebraicComplexity.Examples.cwSortedPair112ResidualCyclicPower_degenerates_squareFamilies
