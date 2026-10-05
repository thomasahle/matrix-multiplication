/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.CoarsenedSupportPreimage

set_option autoImplicit false

/-! # Axiom audit for the coarse-cut / fine-preimage bridge -/

#assert_axioms AlgebraicComplexity.Tensor.mem_coarseningPreimageSupport
#assert_axioms AlgebraicComplexity.Tensor.coarsen_withSupport_preimage_realize_eq
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.coarsen_withSupport_preimage
#assert_axioms AlgebraicComplexity.Tensor.Restricts.coarsen_withSupport_to_preimage
#assert_axioms AlgebraicComplexity.Tensor.withSupport_reindex_refl
#assert_axioms AlgebraicComplexity.Tensor.map_blockAddressCongr_refl
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.withSupport_of_reindex_refl
#assert_axioms AlgebraicComplexity.Tensor.Restricts.coarsenedPositivePower_withSupport_to_preimage
