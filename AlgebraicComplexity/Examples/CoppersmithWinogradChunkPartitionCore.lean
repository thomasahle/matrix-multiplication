/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradPartitionDataCore
import AlgebraicComplexity.Tensor.PartitionedPowerConstituent

/-!
# Dependency-light Coppersmith--Winograd chunk partition

The level-`depth` chunk partition is only a positive partitioned power of the base CW tensor.
Defining it here lets finite support and dimension clients use that object without importing
interface selection, tensor-power relabeling, or asymptotic extraction.  The richer exact-interface
API re-exports the same definition from `CoppersmithWinogradInterfaceCore`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- The `2^depth`-fold positive partitioned power used as one recursive CW chunk. -/
noncomputable def cwChunkPartitionedTensor
    (K : Type u) [CommRing K] (q depth : ℕ) :=
  (cwPartitionedTensor K q).positivePower (2 ^ depth - 1)

end AlgebraicComplexity.Examples
