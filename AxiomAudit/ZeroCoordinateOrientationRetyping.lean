/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateOrientationRetyping
import AxiomAudit.Command

/-!
# Axiom audit for shared-fibre C-tensor retyping on an arbitrary leg

Checks the two support-hypothesis transports through a leg permutation, the ambient retyping of the
permuted certificate, the restriction it certifies, and the constituent count.
-/

open AlgebraicComplexity AlgebraicComplexity.CTensor.FiberRetyping

#assert_axioms injOn_map_permuteBlockAddress
#assert_axioms forall_map_permuteBlockAddress_eq
#assert_axioms ofSharedSupportPermutedAmbient
#assert_axioms restricts_permute_ofSharedSupportPermutedAmbient
#assert_axioms permute_support_card
