/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradExactSelectionCore
import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorExactInsideApproximate

set_option autoImplicit false

/-!
# Exact CW interface terms inside approximate CW interfaces

This module instantiates the generic exact-inside-approximate restriction for the native
Coppersmith--Winograd chunk partition.  It supplies the input-profile bridge needed by an exact
rational extraction: the paper's approximate parent interface can first be zeroed to the chosen
exact complete-split profile, without assuming that a full unselected tensor power was present.

This is only the parent selector.  It does not perform the constituent-stage hash, compatibility
cleanup, or hole repair, and it does not identify the selected constituent with a lower child.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*;
  `papers/sources/2404.16349/constituent.tex:113-147,338-348`.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*, the caveat
  that the mixed cyclic assembly does not provide its local input-profile restrictions,
  `better_bound/paper.tex:2034-2036`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- **The approximate CW parent interface restricts to its exact rational type.**

Proof sketch: both tensors are the generic selectors on `cwChunkPartitionedTensor`, using
`cwChunkSplitWord` as the native encoding.  The generic exact-inside-approximate theorem supplies
the legwise zeroing map. -/
theorem cwSelectedApproximateInterfaceTerm_restricts_exact
    {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    Restricts
      ((cwChunkPartitionedTensor K q depth).selectEncodedApproximateInterfaceTerm
        (fun _c ↦ cwChunkSplitWord depth)
        (term.toSemantic (hmultiplicity.symm ▸ Nat.zero_lt_succ n))
        (by simpa using hmultiplicity) epsilon).realize
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize := by
  exact Tensor.Restricts.selectEncodedApproximateInterfaceTerm_to_exact
    (cwChunkPartitionedTensor K q depth) (fun _c ↦ cwChunkSplitWord depth)
      term hmultiplicity hepsilon

end AlgebraicComplexity.Examples
