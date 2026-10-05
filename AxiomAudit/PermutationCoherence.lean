/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PermutationCoherence
import AxiomAudit.Command

/-!
# Axiom audit for tensor permutation coherence
-/

open AlgebraicComplexity.Tensor

#assert_axioms permute_composite_apply
#assert_axioms Isomorphic.permute_orientation_congr
#assert_axioms Isomorphic.cancel_permute_refl
#assert_axioms Isomorphic.cancel_permute_symm_left
#assert_axioms Isomorphic.cancel_permute_symm_right
