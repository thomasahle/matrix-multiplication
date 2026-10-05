/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MarkedModeledFiberRepair
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for repair after marked partitioned-power isolation

This audit covers the generic composition of marked affine isolation, honest pointwise damaged-box
normalization, and finite seven-branch repair.  The damaged-copy argument is the one used in
[alman2025more], `papers/sources/2404.16349/constituent.tex:338-348,473-497`.
-/

#assert_axioms AlgebraicComplexity.Tensor.Restricts.modeledTargets_to_repairedMarkedLegwiseIsolatedIndexedDirectSum
