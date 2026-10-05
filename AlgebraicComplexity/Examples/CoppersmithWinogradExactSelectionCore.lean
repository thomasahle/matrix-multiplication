/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradChunkPartitionCore
import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordCore
import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorSelectionCore

/-!
# Lightweight exact selection for recursive CW interface terms

This module combines the native CW chunk partition and split-word encoding with the generic
finite exact-profile selector.  It deliberately omits position relabelings and tensor-power
restriction witnesses, so dimension clients do not import the heavier realization layer.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- Realize any exact level-`depth + 1` CW interface term by complete-split selection from a
positive power of the chunk partition. -/
noncomputable def cwSelectedExactInterfaceTerm {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :=
  (cwChunkPartitionedTensor K q depth).selectEncodedExactInterfaceTerm
    (fun _c ↦ cwChunkSplitWord depth) term hmultiplicity

end AlgebraicComplexity.Examples
