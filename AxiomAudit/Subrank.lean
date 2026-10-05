/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.Subrank

set_option autoImplicit false

/-!
# Axiom audit for the subrank comparison chain

Focused trust audit for `AlgebraicComplexity/Tensor/Subrank.lean`, which defines the subrank
`Q(T)` -- the largest diagonal tensor `T` restricts onto -- following V. Strassen, *Relative
bilinear complexity and matrix multiplication*, J. reine angew. Math. **375/376** (1987),
406--443, and T. Tao's symmetric formulation of the slice-rank method.

Asserted here is the comparison chain `Q ≤ S ≤ R` that the `README.md` Results row for the
subrank names; the surrounding diagonal-product and supermultiplicativity lemmas are asserted by
the umbrella audit.
-/

#assert_axioms AlgebraicComplexity.Tensor.subrank_le_sliceRank
#assert_axioms AlgebraicComplexity.Tensor.subrank_le_rank
